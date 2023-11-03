#!/usr/bin/env python
# -*- coding: utf-8 -*-
# Description: daemon to submit jobs and retrieve results to/from remote
#              servers
# 
import os
import sys
import site
import sqlite3

rundir = os.path.dirname(os.path.realpath(__file__))
webserver_root = os.path.realpath("%s/../../../"%(rundir))

activate_env="%s/env/bin/activate_this.py"%(webserver_root)
exec(compile(open(activate_env, "rb").read(), activate_env, 'exec'), dict(__file__=activate_env))

from libpredweb import myfunc
from libpredweb import webserver_common as webcom
import time
from datetime import datetime
from dateutil import parser as dtparser
from pytz import timezone
import requests
import json
import urllib.request, urllib.parse, urllib.error
import shutil
import hashlib
from suds.client import Client
import subprocess
import numpy

from geoip import geolite2
import pycountry

TZ = webcom.TZ
os.environ['TZ'] = TZ
time.tzset()

vip_user_list = [
        "nanjiang.shu@scilifelab.se"
        ]

# make sure that only one instance of the script is running
# this code is working 
progname = os.path.basename(__file__)
rootname_progname = os.path.splitext(progname)[0]
lockname = os.path.realpath(__file__).replace(" ", "").replace("/", "-")
import fcntl
lock_file = "/tmp/%s.lock"%(lockname)
fp = open(lock_file, 'w')
try:
    fcntl.lockf(fp, fcntl.LOCK_EX | fcntl.LOCK_NB)
except IOError:
    print("Another instance of %s is running"%(progname), file=sys.stderr)
    sys.exit(1)

contact_email = "nanjiang.shu@scilifelab.se"

threshold_logfilesize = 20*1024*1024

usage_short="""
Usage: %s
"""%(sys.argv[0])

usage_ext="""
Description:
    Daemon to submit jobs and retrieve results to/from remote servers
    run periodically
    At the end of each run generate a runlog file with the status of all jobs

OPTIONS:
  -h, --help    Print this help message and exit

Created 2015-03-25, updated 2015-03-25, Nanjiang Shu
"""
usage_exp="""
"""

basedir = os.path.realpath("%s/.."%(rundir)) # path of the application, i.e. pred/
path_static = "%s/static"%(basedir)
path_log = "%s/static/log"%(basedir)
path_stat = "%s/stat"%(path_log)
path_result = "%s/static/result"%(basedir)
path_cache = "%s/static/result/cache"%(basedir)

# format of the computenodefile is 
# each line is a record and contains two items
# hostname MAX_ALLOWED_PARALLEL_JOBS
computenodefile = "%s/config/computenode.txt"%(basedir)
db_cache_SCAMPI2MSA = "%s/cache_msa.sqlite3"%(path_result)
dbmsa_tablename = "scampi2msa"

gen_errfile = "%s/static/log/%s.err"%(basedir, progname)
gen_logfile = "%s/static/log/%s.log"%(basedir, progname)
black_iplist_file = "%s/config/black_iplist.txt"%(basedir)

def PrintHelp(fpout=sys.stdout):#{{{
    print(usage_short, file=fpout)
    print(usage_ext, file=fpout)
    print(usage_exp, file=fpout)#}}}

def get_job_status(jobid):#{{{
    status = "";
    rstdir = "%s/%s"%(path_result, jobid)
    starttagfile = "%s/%s"%(rstdir, "runjob.start")
    finishtagfile = "%s/%s"%(rstdir, "runjob.finish")
    failedtagfile = "%s/%s"%(rstdir, "runjob.failed")
    if os.path.exists(failedtagfile):
        status = "Failed"
    elif os.path.exists(finishtagfile):
        status = "Finished"
    elif os.path.exists(starttagfile):
        status = "Running"
    elif os.path.exists(rstdir):
        status = "Wait"
    return status
#}}}
def get_total_seconds(td): #{{{
    """
    return the total_seconds for the timedate.timedelta object
    for python version >2.7 this is not needed
    """
    return (td.microseconds + (td.seconds + td.days * 24 * 3600) * 1e6) / 1e6
#}}}
def GetNumSuqJob(node):#{{{
    # get the number of queueing jobs on the node
    # return -1 if the url is not accessible
    url = "http://%s/cgi-bin/get_suqlist.cgi?base=log"%(node)
    try:
        rtValue = requests.get(url, timeout=2)
        if rtValue.status_code < 400:
            lines = rtValue.content.split("\n")
            cnt_queue_job = 0
            for line in lines:
                strs = line.split()
                if len(strs)>=4 and strs[0].isdigit():
                    status = strs[2]
                    if status == "Wait":
                        cnt_queue_job += 1
            return cnt_queue_job
        else:
            return -1
    except:
        date_str = time.strftime(g_params['FORMAT_DATETIME'])
        myfunc.WriteFile("[Date: %s] requests.get(%s) failed\n"%(date_str,
            url), gen_errfile, "a", True)
        return -1

#}}}
def GetNumSeqSameUserDict(joblist):#{{{
# calculate the number of sequences for each user in the queue or running
# Fixed error for getting numseq at 2015-04-11
    numseq_user_dict = {}
    for i in range(len(joblist)):
        li1 = joblist[i]
        jobid1 = li1[0]
        ip1 = li1[3]
        email1 = li1[4]
        try:
            numseq1 = int(li1[5])
        except:
            numseq1 = 123
            pass
        if not jobid1 in numseq_user_dict:
            numseq_user_dict[jobid1] = 0
        numseq_user_dict[jobid1] += numseq1
        if ip1 == "" and email1 == "":
            continue

        for j in range(len(joblist)):
            li2 = joblist[j]
            if i == j:
                continue

            jobid2 = li2[0]
            ip2 = li2[3]
            email2 = li2[4]
            try:
                numseq2 = int(li2[5])
            except:
                numseq2 = 123
                pass
            if ((ip2 != "" and ip2 == ip1) or
                    (email2 != "" and email2 == email1)):
                numseq_user_dict[jobid1] += numseq2
    return numseq_user_dict
#}}}
def CreateRunJoblog(path_result, submitjoblogfile, runjoblogfile,#{{{
        finishedjoblogfile, loop):
    myfunc.WriteFile("CreateRunJoblog...\n", gen_logfile, "a", True)
    # Read entries from submitjoblogfile, checking in the result folder and
    # generate two logfiles: 
    #   1. runjoblogfile 
    #   2. finishedjoblogfile
    # when loop == 0, for unfinished jobs, re-generate finished_seqs.txt
    hdl = myfunc.ReadLineByBlock(submitjoblogfile)
    if hdl.failure:
        return 1

    finished_jobid_list = []
    finished_job_dict = {}
    if os.path.exists(finishedjoblogfile):
        finished_job_dict = myfunc.ReadFinishedJobLog(finishedjoblogfile)

    new_finished_list = []  # Finished or Failed
    new_submitted_list = []  # 

    new_runjob_list = []    # Running
    new_waitjob_list = []    # Queued
    lines = hdl.readlines()
    while lines != None:
        for line in lines:
            strs = line.split("\t")
            if len(strs) < 8:
                continue
            submit_date_str = strs[0]
            jobid = strs[1]
            ip = strs[2]
            numseq_str = strs[3]
            jobname = strs[5]
            email = strs[6].strip()
            method_submission = strs[7]
            start_date_str = ""
            finish_date_str = ""
            rstdir = "%s/%s"%(path_result, jobid)

            numseq = 1
            try:
                numseq = int(numseq_str)
            except:
                pass

            isRstFolderExist = False
            if os.path.exists(rstdir):
                isRstFolderExist = True


            if isRstFolderExist:
                new_submitted_list.append([jobid,line])

            if jobid in finished_job_dict:
                if isRstFolderExist:
                    li = [jobid] + finished_job_dict[jobid]
                    new_finished_list.append(li)
                continue


            status = get_job_status(jobid)
            if g_params['DEBUG']:
                myfunc.WriteFile("DEBUG: %s status=%s\n"%(jobid, status), gen_logfile, "a", True)

            starttagfile = "%s/%s"%(rstdir, "runjob.start")
            finishtagfile = "%s/%s"%(rstdir, "runjob.finish")
            if os.path.exists(starttagfile):
                start_date_str = myfunc.ReadFile(starttagfile).strip().rstrip("CEST")
            if os.path.exists(finishtagfile):
                finish_date_str = myfunc.ReadFile(finishtagfile).strip().rstrip("CEST")

            jobinfofile = "%s/jobinfo"%(rstdir)
            jobinfo = myfunc.ReadFile(jobinfofile).strip()
            jobinfolist = jobinfo.split("\t")
            app_type = "None"
            if len(jobinfolist) >= 9:
                app_type = jobinfolist[8]

            # li has  11 fields, one more compared to other web-servers, such as TOPCONS2
            li = [jobid, status, jobname, ip, email, numseq_str,
                    method_submission, submit_date_str, start_date_str,
                    finish_date_str, app_type] 

            if status in ["Finished", "Failed"]:
                new_finished_list.append(li)

            # single-sequence job submitted from the web-page will be
            # submmitted by suq
            UPPER_WAIT_TIME_IN_SEC = 60
            isValidSubmitDate = True
            try:
                submit_date = webcom.datetime_str_to_time(submit_date_str)
            except ValueError:
                isValidSubmitDate = False

            if isValidSubmitDate:
                current_time = datetime.now(timezone(TZ))
                timeDiff = current_time - submit_date
                queuetime_in_sec = timeDiff.seconds
            else:
                queuetime_in_sec = UPPER_WAIT_TIME_IN_SEC + 1

            if numseq >= 1 or method_submission == "wsdl" or queuetime_in_sec > UPPER_WAIT_TIME_IN_SEC:
                if status == "Running":
                    new_runjob_list.append(li)
                elif status == "Wait":
                    new_waitjob_list.append(li)
        lines = hdl.readlines()
    hdl.close()

# re-write logs of submitted jobs
    li_str = []
    for li in new_submitted_list:
        li_str.append(li[1])
    if len(li_str)>0:
        myfunc.WriteFile("\n".join(li_str)+"\n", submitjoblogfile, "w", True)
    else:
        myfunc.WriteFile("", submitjoblogfile, "w", True)

# re-write logs of finished jobs
    li_str = []
    for li in new_finished_list:
        li = [str(x) for x in li]
        li_str.append("\t".join(li))
    if len(li_str)>0:
        myfunc.WriteFile("\n".join(li_str)+"\n", finishedjoblogfile, "w", True)
    else:
        myfunc.WriteFile("", finishedjoblogfile, "w", True)
# re-write logs of finished jobs for each IP
    new_finished_dict = {}
    for li in new_finished_list:
        ip = li[3]
        if not ip in new_finished_dict:
            new_finished_dict[ip] = []
        new_finished_dict[ip].append(li)
    for ip in new_finished_dict:
        finished_list_for_this_ip = new_finished_dict[ip]
        divide_finishedjoblogfile = "%s/divided/%s_finished_job.log"%(path_log,
                ip)
        li_str = []
        for li in finished_list_for_this_ip:
            li = [str(x) for x in li]
            li_str.append("\t".join(li))
        if len(li_str)>0:
            myfunc.WriteFile("\n".join(li_str)+"\n", divide_finishedjoblogfile, "w", True)
        else:
            myfunc.WriteFile("", divide_finishedjoblogfile, "w", True)

# update allfinished jobs
    allfinishedjoblogfile = "%s/all_finished_job.log"%(path_log)
    allfinished_jobid_set = myfunc.ReadIDList2(allfinishedjoblogfile, col=0, delim="\t")
    li_str = []
    for li in new_finished_list:
        li = [str(x) for x in li]
        jobid = li[0]
        if not jobid in allfinished_jobid_set:
            li_str.append("\t".join(li))
    if len(li_str)>0:
        myfunc.WriteFile("\n".join(li_str)+"\n", allfinishedjoblogfile, "a", True)

# update all_submitted jobs
    allsubmitjoblogfile = "%s/all_submitted_seq.log"%(path_log)
    allsubmitted_jobid_set = set(myfunc.ReadIDList2(allsubmitjoblogfile, col=1, delim="\t"))
    li_str = []
    for li in new_submitted_list:
        jobid = li[0]
        if not jobid in allsubmitted_jobid_set:
            li_str.append(li[1])
    if len(li_str)>0:
        myfunc.WriteFile("\n".join(li_str)+"\n", allsubmitjoblogfile, "a", True)

# write logs of running and queuing jobs
# the queuing jobs are sorted in descending order by the suq priority
# frist get numseq_this_user for each jobs
# format of numseq_this_user: {'jobid': numseq_this_user}
    numseq_user_dict = GetNumSeqSameUserDict(new_runjob_list + new_waitjob_list)

# now append numseq_this_user and priority score to new_waitjob_list and
# new_runjob_list

    for joblist in [new_waitjob_list, new_runjob_list]:
        for li in joblist:
            jobid = li[0]
            ip = li[3]
            email = li[4].strip()
            rstdir = "%s/%s"%(path_result, jobid)
            outpath_result = "%s/%s"%(rstdir, jobid)
            try:
                numseq = int(li[5])
            except:
                numseq = 1
                pass
            try:
                numseq_this_user = numseq_user_dict[jobid]
            except:
                numseq_this_user = numseq
                pass

            # if loop == 0 , for new_waitjob_list and new_runjob_list
            # re-generate finished_seqs.txt
            if loop == 0 and os.path.exists(outpath_result):#{{{
                finished_seq_file = "%s/finished_seqs.txt"%(outpath_result)
                finished_idx_file = "%s/finished_seqindex.txt"%(rstdir)
                torun_idx_file = "%s/torun_seqindex.txt"%(rstdir) # ordered seq index to run
                finished_idx_set = set([])

                finished_seqs_idlist = []
                if os.path.exists(finished_seq_file):
                    finished_seqs_idlist = myfunc.ReadIDList2(finished_seq_file, col=0, delim="\t")
                finished_seqs_idset = set(finished_seqs_idlist)
                for finished_id in finished_seqs_idset:
                    origIndex_str = finished_id.split("_")[1]
                    finished_idx_set.add(origIndex_str)

                all_idx_list = [str(x) for x in range(numseq)]
                torun_idx_str_list = list(set(all_idx_list)-finished_idx_set)

                if len(finished_idx_set) > 0:
                    myfunc.WriteFile("\n".join(list(finished_idx_set))+"\n", finished_idx_file, "w", True)
                else:
                    myfunc.WriteFile("", finished_idx_file, "w", True)

                if len(torun_idx_str_list) > 0:
                    myfunc.WriteFile("\n".join(list(torun_idx_str_list))+"\n", torun_idx_file, "w", True)
                else:
                    myfunc.WriteFile("", torun_idx_file, "w", True)


            #}}}

            # note that the priority is deducted by numseq so that for jobs
            # from the same user, jobs with fewer sequences are placed with
            # higher priority
            priority = myfunc.GetSuqPriority(numseq_this_user) - numseq

            if ip in g_params['blackiplist']:
                priority = priority/1000.0

            if email in vip_user_list:
                numseq_this_user = 1
                priority = 999999999.0
                myfunc.WriteFile("email %s in vip_user_list\n"%(email), gen_logfile, "a", True)

            li.append(numseq_this_user) #12th field
            li.append(priority)         #13th field


    # sort the new_waitjob_list in descending order by priority
    new_waitjob_list = sorted(new_waitjob_list, key=lambda x:x[12], reverse=True)
    new_runjob_list = sorted(new_runjob_list, key=lambda x:x[12], reverse=True)

    # write to runjoblogfile
    li_str = []
    for joblist in [new_waitjob_list, new_runjob_list]:
        for li in joblist:
            li2 = li[:11]+[str(li[11]), str(li[12])]
            li_str.append("\t".join(li2))
#     print "write to", runjoblogfile
#     print "\n".join(li_str)
    if len(li_str)>0:
        myfunc.WriteFile("\n".join(li_str)+"\n", runjoblogfile, "w", True)
    else:
        myfunc.WriteFile("", runjoblogfile, "w", True)

#}}}
def SubmitJob(jobid, cntSubmitJobDict, numseq_this_user):#{{{
# for each job rstdir, keep three log files, 
# 1.seqs finished, finished_seq log keeps all information, finished_index_log
#   can be very compact to speed up reading, e.g.
#   1-5 7-9 etc
# 2.seqs queued remotely , format:
#       index node remote_jobid
# 3. format of the torun_idx_file
#    origIndex

    rmsg = ""
    myfunc.WriteFile("SubmitJob for %s, numseq_this_user=%d\n"%(jobid,
        numseq_this_user), gen_logfile, "a", True)
    rstdir = "%s/%s"%(path_result, jobid)
    outpath_result = "%s/%s"%(rstdir, jobid)
    if not os.path.exists(outpath_result):
        os.mkdir(outpath_result)

    finished_idx_file = "%s/finished_seqindex.txt"%(rstdir)
    failed_idx_file = "%s/failed_seqindex.txt"%(rstdir)
    remotequeue_idx_file = "%s/remotequeue_seqindex.txt"%(rstdir)
    torun_idx_file = "%s/torun_seqindex.txt"%(rstdir) # ordered seq index to run
    cnttry_idx_file = "%s/cntsubmittry_seqindex.txt"%(rstdir)#index file to keep log of tries

    runjob_errfile = "%s/%s"%(rstdir, "runjob.err")
    runjob_logfile = "%s/%s"%(rstdir, "runjob.log")
    finished_seq_file = "%s/finished_seqs.txt"%(outpath_result)
    tmpdir = "%s/tmpdir"%(rstdir)
    qdinittagfile = "%s/runjob.qdinit"%(rstdir)
    qdinit_start_tagfile = "%s/runjob.qdinit.start"%(rstdir)
    failedtagfile = "%s/%s"%(rstdir, "runjob.failed")
    starttagfile = "%s/%s"%(rstdir, "runjob.start")
    fafile = "%s/query.fa"%(rstdir)
    split_seq_dir = "%s/splitaa"%(tmpdir)
    forceruntagfile = "%s/forcerun"%(rstdir)

    finished_idx_list = []
    failed_idx_list = []    # [origIndex]
    if os.path.exists(finished_idx_file):
        finished_idx_list = list(set(myfunc.ReadIDList(finished_idx_file)))
    if os.path.exists(failed_idx_file):
        failed_idx_list = list(set(myfunc.ReadIDList(failed_idx_file)))

    processed_idx_set = set(finished_idx_list) | set(failed_idx_list)

    jobinfofile = "%s/jobinfo"%(rstdir)
    jobinfo = ""
    if os.path.exists(jobinfofile):
        jobinfo = myfunc.ReadFile(jobinfofile).strip()
    jobinfolist = jobinfo.split("\t")
    email = ""
    if len(jobinfolist) >= 8:
        email = jobinfolist[6]
        method_submission = jobinfolist[7]

    # the first time when the this jobid is processed, do the following
    # 1. generate a file with sorted seqindex
    # 2. generate splitted sequence files named by the original seqindex
    if not os.path.exists(qdinittagfile): #initialization#{{{
        date_str = time.strftime(g_params['FORMAT_DATETIME'])
        myfunc.WriteFile(date_str, qdinit_start_tagfile, "w", True)
        if not os.path.exists(starttagfile):
            myfunc.WriteFile(date_str, starttagfile, "w", True)
        if not os.path.exists(tmpdir):
            os.mkdir(tmpdir)

        init_finished_idx_list = [] # [origIndex]
        if os.path.exists(finished_idx_file):
            init_finished_idx_list = myfunc.ReadIDList(finished_idx_file)

        init_finished_idx_set = set(init_finished_idx_list)
        if g_params['DEBUG']:
            myfunc.WriteFile("DEBUG: init_finished_idx_list = %s"%(str(init_finished_idx_list)), gen_logfile, "a", True)

        # ==== 1.dealing with cached results 
        (seqIDList, seqAnnoList, seqList) = myfunc.ReadFasta(fafile)
        if len(seqIDList) <= 0:
            date_str = time.strftime(g_params['FORMAT_DATETIME'])
            myfunc.WriteFile(date_str, failedtagfile, "w", True)
            myfunc.WriteFile("Read query seq file failed. Zero sequence read in.\n", runjob_errfile, "a", True)
            return 1
        toRunDict = {}
        if os.path.exists(forceruntagfile):
            for i in range(len(seqIDList)):
                toRunDict[i] = [seqList[i], 0, seqAnnoList[i]]
        else:
            con = sqlite3.connect(db_cache_SCAMPI2MSA)
            with con:
                cur = con.cursor()
                cur.execute("""
                    CREATE TABLE IF NOT EXISTS %s
                    (
                        md5 VARCHAR(100),
                        seq VARCHAR(30000),
                        top VARCHAR(30000),
                        PRIMARY KEY (md5)
                    )"""%(dbmsa_tablename))
            for i in range(len(seqIDList)):
                seq = seqList[i]
                description = seqAnnoList[i]
                if not str(i) in init_finished_idx_set:
                    isSkip = False
                    md5_key = hashlib.md5(seq.encode('utf-8')).hexdigest()
                    cmd =  "SELECT md5, seq, top FROM %s WHERE md5 =  \"%s\""%(
                            dbmsa_tablename, md5_key)
                    cur.execute(cmd)
                    rows = cur.fetchall()
                    for row in rows:
                        top = row[2]
                        numTM = myfunc.CountTM(top)
                        # info_finish has 8 items
                        info_finish = [ "seq_%d"%i, str(len(seq)), str(numTM),
                                "cached", str(0.0), description, seq, top]
                        myfunc.WriteFile("\t".join(info_finish)+"\n",
                                finished_seq_file, "a", isFlush=True)
                        myfunc.WriteFile("%d\n"%(i), finished_idx_file, "a", isFlush=True)
                        isSkip = True
                    if not isSkip:
                        toRunDict[i] = [seqList[i], 0, seqAnnoList[i]] #init value for numTM is 0

        sortedlist = sorted(list(toRunDict.items()), key=lambda x:x[1][1], reverse=True)

        # Write splitted fasta file and write a torunlist.txt
        if not os.path.exists(split_seq_dir):
            os.mkdir(split_seq_dir)

        torun_index_str_list = [str(x[0]) for x in sortedlist]
        if len(torun_index_str_list)>0:
            myfunc.WriteFile("\n".join(torun_index_str_list)+"\n", torun_idx_file, "w", True)
        else:
            myfunc.WriteFile("", torun_idx_file, "w", True)

        # write cnttry file for each jobs to run
        cntTryDict = {}
        for idx in torun_index_str_list:
            cntTryDict[int(idx)] = 0
        json.dump(cntTryDict, open(cnttry_idx_file, "w"))

        for item in sortedlist:
            origIndex = item[0]
            seq = item[1][0]
            description = item[1][2]
            seqfile_this_seq = "%s/%s"%(split_seq_dir, "query_%d.fa"%(origIndex))
            seqcontent = ">%s\n%s\n"%(description, seq)
            myfunc.WriteFile(seqcontent, seqfile_this_seq, "w", True)
        # qdinit file is written at the end of initialization, to make sure
        # that initialization is either not started or completed
        date_str = time.strftime(g_params['FORMAT_DATETIME'])
        myfunc.WriteFile(date_str, qdinittagfile, "w", True)
#}}}


    # 3. try to submit the job 
    if os.path.exists(forceruntagfile):
        isforcerun = "True"
    else:
        isforcerun = "False"
    toRunIndexList = [] # index in str
    processedIndexSet = set([]) #seq index set that are already processed
    submitted_loginfo_list = []
    if os.path.exists(torun_idx_file):
        toRunIndexList = myfunc.ReadIDList(torun_idx_file)
        # unique the list but keep the order
        toRunIndexList = myfunc.uniquelist(toRunIndexList)
    if len(toRunIndexList) > 0:
        iToRun = 0
        numToRun = len(toRunIndexList)
        for node in cntSubmitJobDict:
            if iToRun >= numToRun:
                break
            wsdl_url = "http://%s/pred/api_submitseq/?wsdl"%(node)
            try:
                myclient = Client(wsdl_url, cache=None, timeout=30)
            except Exception as e:
                date_str = time.strftime(g_params['FORMAT_DATETIME'])
                myfunc.WriteFile("[Date: %s] Failed to access %s with errmsg %s\n"%(date_str,
                    wsdl_url, str(e)), gen_errfile, "a", True)
                break

            [cnt, maxnum, queue_method, node_status] = cntSubmitJobDict[node]
            MAX_SUBMIT_TRY = 3
            cnttry = 0
            while cnt < maxnum and iToRun < numToRun:
                origIndex = int(toRunIndexList[iToRun])
                seqfile_this_seq = "%s/%s"%(split_seq_dir, "query_%d.fa"%(origIndex))
                # ignore already existing query seq, this is an ugly solution,
                # the generation of torunindexlist has a bug
                outpath_this_seq = "%s/%s"%(outpath_result, "seq_%d"%origIndex)
                if os.path.exists(outpath_this_seq):
                    iToRun += 1
                    continue


                if g_params['DEBUG']:
                    myfunc.WriteFile("DEBUG: cnt (%d) < maxnum (%d) "\
                            "and iToRun(%d) < numToRun(%d)"%(cnt, maxnum, iToRun, numToRun), gen_logfile, "a", True)
                fastaseq = ""
                seqid = ""
                seqanno = ""
                seq = ""
                if not os.path.exists(seqfile_this_seq):
                    all_seqfile = "%s/query.fa"%(rstdir)
                    try:
                        (allseqidlist, allannolist, allseqlist) = myfunc.ReadFasta(all_seqfile)
                        seqid = allseqidlist[origIndex]
                        seqanno = allannolist[origIndex]
                        seq = allseqlist[origIndex]
                        fastaseq = ">%s\n%s\n"%(seqanno, seq)
                    except:
                        pass
                else:
                    fastaseq = myfunc.ReadFile(seqfile_this_seq)#seq text in fasta format
                    (seqid, seqanno, seq) = myfunc.ReadSingleFasta(seqfile_this_seq)


                isSubmitSuccess = False
                if len(seq) > 0:
                    query_para = {}
                    query_para['name_software'] = "scampi2-msa"
                    query_para['queue_method'] = queue_method

                    para_str = json.dumps(query_para, sort_keys=True)
                    jobname = ""
                    if not email in vip_user_list:
                        useemail = ""
                    else:
                        useemail = email
                    try:
                        myfunc.WriteFile("\tSubmitting seq %4d "%(origIndex),
                                gen_logfile, "a", True)
                        rtValue = myclient.service.submitjob_remote(fastaseq, para_str,
                                jobname, useemail, str(numseq_this_user), isforcerun)
                    except:
                        date_str = time.strftime(g_params['FORMAT_DATETIME'])
                        myfunc.WriteFile("[Date: %s] Failed to run myclient.service.submitjob_remote\n"%(date_str), gen_errfile, "a", True)
                        rtValue = []
                        pass

                    cnttry += 1
                    if len(rtValue) >= 1:
                        strs = rtValue[0]
                        if len(strs) >=5:
                            remote_jobid = strs[0]
                            result_url = strs[1]
                            numseq_str = strs[2]
                            errinfo = strs[3]
                            warninfo = strs[4]
                            if remote_jobid != "None" and remote_jobid != "":
                                isSubmitSuccess = True
                                epochtime = time.time()
                                # 6 fields in the file remotequeue_idx_file
                                txt =  "%d\t%s\t%s\t%s\t%s\t%f"%( origIndex,
                                        node, remote_jobid, seqanno, seq,
                                        epochtime)
                                submitted_loginfo_list.append(txt)
                                cnttry = 0  #reset cnttry to zero
                        else:
                            date_str = time.strftime(g_params['FORMAT_DATETIME'])
                            myfunc.WriteFile("[Date: %s] bad wsdl return value\n"%(date_str), gen_errfile, "a", True)
                if isSubmitSuccess:
                    cnt += 1
                    myfunc.WriteFile(" succeeded\n", gen_logfile, "a", True)
                else:
                    myfunc.WriteFile(" failed\n", gen_logfile, "a", True)

                if isSubmitSuccess or cnttry >= MAX_SUBMIT_TRY:
                    iToRun += 1
                    processedIndexSet.add(str(origIndex))
                    if g_params['DEBUG']:
                        myfunc.WriteFile("DEBUG: jobid %s processedIndexSet.add(str(%d))\n"%(jobid, origIndex), gen_logfile, "a", True)
            # update cntSubmitJobDict for this node
            cntSubmitJobDict[node][0] = cnt

    # finally, append submitted_loginfo_list to remotequeue_idx_file 
    if len(submitted_loginfo_list)>0:
        myfunc.WriteFile("\n".join(submitted_loginfo_list)+"\n", remotequeue_idx_file, "a", True)
    # update torun_idx_file
    newToRunIndexList = []
    for idx in toRunIndexList:
        if not idx in processedIndexSet:
            newToRunIndexList.append(idx)
    if g_params['DEBUG']:
        myfunc.WriteFile("DEBUG: jobid %s, newToRunIndexList="%(jobid) + " ".join( newToRunIndexList)+"\n", gen_logfile, "a", True)

    if len(newToRunIndexList)>0:
        myfunc.WriteFile("\n".join(newToRunIndexList)+"\n", torun_idx_file, "w", True)
    else:
        myfunc.WriteFile("", torun_idx_file, "w", True)

    return 0
#}}}
def GetResult(jobid):#{{{
    # retrieving result from the remote server for this job
    myfunc.WriteFile("GetResult for %s.\n" %(jobid), gen_logfile, "a", True)
    rstdir = "%s/%s"%(path_result, jobid)
    outpath_result = "%s/%s"%(rstdir, jobid)
    if not os.path.exists(outpath_result):
        os.mkdir(outpath_result)

    remotequeue_idx_file = "%s/remotequeue_seqindex.txt"%(rstdir)

    torun_idx_file = "%s/torun_seqindex.txt"%(rstdir) # ordered seq index to run
    finished_idx_file = "%s/finished_seqindex.txt"%(rstdir)
    failed_idx_file = "%s/failed_seqindex.txt"%(rstdir)

    starttagfile = "%s/%s"%(rstdir, "runjob.start")
    cnttry_idx_file = "%s/cntsubmittry_seqindex.txt"%(rstdir)#index file to keep log of tries
    tmpdir = "%s/tmpdir"%(rstdir)
    finished_seq_file = "%s/finished_seqs.txt"%(outpath_result)

    finished_info_list = [] #[info for finished record]
    finished_idx_list = [] # [origIndex]
    failed_idx_list = []    # [origIndex]
    resubmit_idx_list = []  # [origIndex]
    keep_queueline_list = [] # [line] still in queue

    cntTryDict = {}
    if os.path.exists(cnttry_idx_file):
        with open(cnttry_idx_file, 'r') as fpin:
            cntTryDict = json.load(fpin)

    # in case of missing queries, if remotequeue_idx_file is empty  but the job
    # is still not finished, force re-creating torun_idx_file
    if ((not os.path.exists(remotequeue_idx_file) or
        os.path.getsize(remotequeue_idx_file)<1)):
        idlist1 = []
        idlist2 = []
        if os.path.exists(finished_idx_file):
           idlist1 =  myfunc.ReadIDList(finished_idx_file)
        if os.path.exists(failed_idx_file):
           idlist2 =  myfunc.ReadIDList(failed_idx_file)

        completed_idx_set = set(idlist1 + idlist2)

        jobinfofile = "%s/jobinfo"%(rstdir)
        jobinfo = myfunc.ReadFile(jobinfofile).strip()
        jobinfolist = jobinfo.split("\t")
        if len(jobinfolist) >= 8:
            numseq = int(jobinfolist[3])

        if len(completed_idx_set) < numseq:
            all_idx_list = [str(x) for x in range(numseq)]
            torun_idx_str_list = list(set(all_idx_list)-completed_idx_set)
            for idx in torun_idx_str_list:
                try:
                    cntTryDict[int(idx)] += 1
                except:
                    cntTryDict[int(idx)] = 1
                    pass
            myfunc.WriteFile("\n".join(torun_idx_str_list)+"\n", torun_idx_file, "w", True)

            if g_params['DEBUG']:
                myfunc.WriteFile("recreate torun_idx_file: jobid = %s, numseq=%d, len(completed_idx_set)=%d, len(torun_idx_str_list)=%d\n"%(jobid, numseq, len(completed_idx_set), len(torun_idx_str_list)), gen_logfile, "a", True)
        else:
            myfunc.WriteFile("", torun_idx_file, "w", True)

    text = ""
    if os.path.exists(remotequeue_idx_file):
        text = myfunc.ReadFile(remotequeue_idx_file)
    if text == "":
        return 1
    lines = text.split("\n")

    nodeSet = set([])
    for i in range(len(lines)):
        line = lines[i]
        if not line or line[0] == "#":
            continue
        strs = line.split("\t")
        if len(strs) != 6:
            continue
        node = strs[1]
        nodeSet.add(node)

    myclientDict = {}
    for node in nodeSet:
        wsdl_url = "http://%s/pred/api_submitseq/?wsdl"%(node)
        try:
            myclient = Client(wsdl_url, cache=None, timeout=30)
            myclientDict[node] = myclient
        except:
            date_str = time.strftime(g_params['FORMAT_DATETIME'])
            myfunc.WriteFile("[Date: %s] Failed to access %s\n"%(date_str, wsdl_url), gen_errfile, "a", True)
            pass


    for i in range(len(lines)):#{{{
        line = lines[i]

        if g_params['DEBUG']:
            myfunc.WriteFile("Process %s\n"%(line), gen_logfile, "a", True)
        if not line or line[0] == "#":
            continue
        strs = line.split("\t")
        if len(strs) != 6:
            continue
        origIndex = int(strs[0])
        node = strs[1]
        remote_jobid = strs[2]
        description = strs[3]
        seq = strs[4]
        submit_time_epoch = float(strs[5])
        subfoldername_this_seq = "seq_%d"%(origIndex)
        outpath_this_seq = "%s/%s"%(outpath_result, "seq_%d"%origIndex)

        try:
            myclient = myclientDict[node]
        except KeyError:
            continue
        try:
            rtValue = myclient.service.checkjob(remote_jobid)
        except:
            date_str = time.strftime(g_params['FORMAT_DATETIME'])
            myfunc.WriteFile("[Date: %s] Failed to run myclient.service.checkjob(%s)\n"%(date_str, remote_jobid), gen_errfile, "a", True)
            rtValue = []
            pass
        isSuccess = False
        isFinish_remote = False
        if len(rtValue) >= 1:
            ss2 = rtValue[0]
            if len(ss2)>=3:
                status = ss2[0]
                result_url = ss2[1]
                errinfo = ss2[2]

                if errinfo and errinfo.find("does not exist")!=-1:
                    isFinish_remote = True

                if status == "Finished":#{{{
                    isFinish_remote = True
                    outfile_zip = "%s/%s.zip"%(tmpdir, remote_jobid)
                    isRetrieveSuccess = False
                    myfunc.WriteFile("\tFetching result for %s "%(result_url),
                            gen_logfile, "a", True)
                    if myfunc.IsURLExist(result_url,timeout=5):
                        try:
                            urllib.request.urlretrieve (result_url, outfile_zip)
                            isRetrieveSuccess = True
                            myfunc.WriteFile(" succeeded\n", gen_logfile, "a", True)
                        except:
                            myfunc.WriteFile(" failed\n", gen_logfile, "a", True)
                            pass
                    if os.path.exists(outfile_zip) and isRetrieveSuccess:
                        cmd = ["unzip", outfile_zip, "-d", tmpdir]
                        webcom.RunCmd(cmd, gen_logfile, gen_errfile)
                        rst_this_seq = "%s/%s/seq_0"%(tmpdir, remote_jobid)

                        if os.path.islink(outpath_this_seq):
                            os.unlink(outpath_this_seq)
                        elif os.path.exists(outpath_this_seq):
                            shutil.rmtree(outpath_this_seq)

                        if os.path.exists(rst_this_seq) and not os.path.exists(outpath_this_seq):
                            cmd = ["mv","-f", rst_this_seq, outpath_this_seq]
                            webcom.RunCmd(cmd, gen_logfile, gen_errfile)
                            if os.path.exists(outpath_this_seq):
                                isSuccess = True

                            if isSuccess:
                                # create or update the md5 cache
                                md5_key = hashlib.md5(seq.encode('utf-8')).hexdigest()
                                predfile = "%s/query.top"%( outpath_this_seq)
                                (seqid, seqanno, top) = myfunc.ReadSingleFasta(predfile)
                                if len(top) == len(seq):
                                    con = sqlite3.connect(db_cache_SCAMPI2MSA)
                                    with con:
                                        cur = con.cursor()
                                        cur.execute("""
                                            CREATE TABLE IF NOT EXISTS %s
                                            (
                                                md5 VARCHAR(100),
                                                seq VARCHAR(30000),
                                                top VARCHAR(30000),
                                                PRIMARY KEY (md5)
                                            )"""%(dbmsa_tablename))
                                        cmd =  "INSERT OR REPLACE INTO %s(md5,  seq, top) VALUES('%s', '%s','%s')"%(dbmsa_tablename, md5_key, seq, top)
                                        cur.execute(cmd)

                                else:
                                    date_str = time.strftime(g_params['FORMAT_DATETIME'])
                                    logmsg = "[Date: %s] bad prediction for %s, len(top)=%d\n"%(
                                            date_str, subfoldername_this_seq, len(top))
                                    myfunc.WriteFile(logmsg, gen_logfile, "a", True)
                                    isSuccess = False

                                # delete the data on the remote server
                                try:
                                    rtValue2 = myclient.service.deletejob(remote_jobid)
                                except:
                                    date_str = time.strftime(g_params['FORMAT_DATETIME'])
                                    myfunc.WriteFile( "[Date: %s] Failed to run myclient.service.deletejob(%s)\n"%(date_str, remote_jobid), gen_errfile, "a", True)
                                    rtValue2 = []
                                    pass

                                logmsg = ""
                                if len(rtValue2) >= 1:
                                    ss2 = rtValue2[0]
                                    if len(ss2) >= 2:
                                        status = ss2[0]
                                        errmsg = ss2[1]
                                        if status == "Succeeded":
                                            logmsg = "Successfully deleted data on %s "\
                                                    "for %s"%(node, remote_jobid)
                                        else:
                                            logmsg = "Failed to delete data on %s for "\
                                                    "%s\nError message:\n%s\n"%(node, remote_jobid, errmsg)
                                else:
                                    logmsg = "Failed to call deletejob %s via WSDL on %s\n"%(remote_jobid, node)

                                # delete the zip file
                                os.remove(outfile_zip)
                                shutil.rmtree("%s/%s"%(tmpdir, remote_jobid))


#}}}
                elif status in ["Failed", "None"]:
                    # the job is failed for this sequence, try to re-submit
                    isFinish_remote = True
                    cnttry = 1
                    try:
                        cnttry = cntTryDict[int(origIndex)]
                    except KeyError:
                        cnttry = 1
                        pass
                    if cnttry < g_params['MAX_RESUBMIT']:
                        resubmit_idx_list.append(str(origIndex))
                        cntTryDict[int(origIndex)] = cnttry+1
                    else:
                        failed_idx_list.append(str(origIndex))
                if status != "Wait" and not os.path.exists(starttagfile):
                    date_str = time.strftime(g_params['FORMAT_DATETIME'])
                    myfunc.WriteFile(date_str, starttagfile, "w", True)

                if g_params['DEBUG_CACHE']:
                    myfunc.WriteFile("\n", gen_logfile, "a", True)

        if isSuccess:#{{{
            time_now = time.time()
            runtime = 5.0
            runtime1 = time_now - submit_time_epoch #in seconds
            timefile = "%s/time.txt"%(outpath_this_seq)
            if os.path.exists(timefile):
                txt = myfunc.ReadFile(timefile).strip()
                ss2 = txt.split(";")
                try:
                    runtime = float(ss2[1])
                except:
                    runtime = runtime1
                    pass
            else:
                runtime = runtime1

            predfile = "%s/query.top"%(outpath_this_seq)
            (seqid, seqanno, top) = myfunc.ReadSingleFasta(predfile)
            numTM = myfunc.CountTM(top)
            info_finish = [ "seq_%d"%origIndex, str(len(seq)), str(numTM),
                    "newrun", str(runtime), description, seq, top]
            myfunc.WriteFile("\t".join(info_finish)+"\n",
                    finished_seq_file, "a", isFlush=True)
            myfunc.WriteFile("%d\n"%(origIndex), finished_idx_file, "a", isFlush=True)
            finished_info_list.append("\t".join(info_finish))
            finished_idx_list.append(str(origIndex))
            shutil.rmtree(outpath_this_seq)
            #}}}

        if not isFinish_remote:
            time_in_remote_queue = time.time() - submit_time_epoch
            # for jobs queued in the remote queue more than one day (but not
            # running) delete it and try to resubmit it. This solved the
            # problem of dead jobs in the remote server due to server
            # rebooting)
            if status != "Running" and time_in_remote_queue > g_params['MAX_TIME_IN_REMOTE_QUEUE']:
                # delete the remote job on the remote server
                try:
                    rtValue2 = myclient.service.deletejob(remote_jobid)
                except Exception as e:
                    date_str = time.strftime(g_params['FORMAT_DATETIME'])
                    myfunc.WriteFile( "[Date: %s] Failed to run myclient.service.deletejob(%s) on node %s with msg %s\n"%(date_str, remote_jobid, node, str(e)), gen_logfile, "a", True)
                    rtValue2 = []
                    pass
            else:
                keep_queueline_list.append(line)
#}}}
    #Finally, write log files
    finished_idx_list = list(set(finished_idx_list))
    failed_idx_list = list(set(failed_idx_list))
    resubmit_idx_list = list(set(resubmit_idx_list))


    if len(failed_idx_list)>0:
        myfunc.WriteFile("\n".join(failed_idx_list)+"\n", failed_idx_file, "a", True)
    if len(resubmit_idx_list)>0:
        myfunc.WriteFile("\n".join(resubmit_idx_list)+"\n", torun_idx_file, "a", True)

    if len(keep_queueline_list)>0:
        myfunc.WriteFile("\n".join(keep_queueline_list)+"\n", remotequeue_idx_file, "w", True);
    else:
        myfunc.WriteFile("", remotequeue_idx_file, "w", True);

    with open(cnttry_idx_file, 'w') as fpout:
        json.dump(cntTryDict, fpout)

    return 0
#}}}

def CheckIfJobFinished(jobid, numseq, email):#{{{
    # check if the job is finished and write tagfiles
    myfunc.WriteFile("CheckIfJobFinished for %s.\n" %(jobid), gen_logfile, "a", True)
    rstdir = "%s/%s"%(path_result, jobid)
    tmpdir = "%s/tmpdir"%(rstdir)
    outpath_result = "%s/%s"%(rstdir, jobid)
    runjob_errfile = "%s/%s"%(rstdir, "runjob.err")
    runjob_logfile = "%s/%s"%(rstdir, "runjob.log")
    finished_idx_file = "%s/finished_seqindex.txt"%(rstdir)
    failed_idx_file = "%s/failed_seqindex.txt"%(rstdir)
    seqfile = "%s/query.fa"%(rstdir)

    base_www_url_file = "%s/static/log/base_www_url.txt"%(basedir)
    base_www_url = ""

    finished_idx_list = []
    failed_idx_list = []
    if os.path.exists(finished_idx_file):
        finished_idx_list = myfunc.ReadIDList(finished_idx_file)
        finished_idx_list = list(set(finished_idx_list))
    if os.path.exists(failed_idx_file):
        failed_idx_list = myfunc.ReadIDList(failed_idx_file)
        failed_idx_list = list(set(failed_idx_list))

    finishtagfile = "%s/%s"%(rstdir, "runjob.finish")
    failedtagfile = "%s/%s"%(rstdir, "runjob.failed")
    starttagfile = "%s/%s"%(rstdir, "runjob.start")

    num_processed = len(finished_idx_list)+len(failed_idx_list)
    finish_status = "" #["success", "failed", "partly_failed"]
    if num_processed >= numseq:# finished
        if len(failed_idx_list) == 0:
            finish_status = "success"
        elif len(failed_idx_list) >= numseq:
            finish_status = "failed"
        else:
            finish_status = "partly_failed"

        if os.path.exists(base_www_url_file):
            base_www_url = myfunc.ReadFile(base_www_url_file).strip()
        if base_www_url == "":
            base_www_url = "http://scampi.bioinfo.se"

        date_str_epoch = time.time()

        # Now write the text output to a single file
        statfile = "%s/%s"%(outpath_result, "stat.txt")
        resultfile_text = "%s/%s"%(outpath_result, "query.top")
        (seqIDList, seqAnnoList, seqList) = myfunc.ReadFasta(seqfile)
        maplist = []
        for i in range(len(seqIDList)):
            maplist.append("%s\t%d\t%s\t%s"%("seq_%d"%i, len(seqList[i]),
                seqAnnoList[i], seqList[i]))
        start_date_str = myfunc.ReadFile(starttagfile).strip().rstrip("CEST").strip()
        start_date_epoch = webcom.datetime_str_to_epoch(start_date_str)
        all_runtime_in_sec = float(date_str_epoch) - float(start_date_epoch)

        webcom.WriteSCAMPI2MSATextResultFile(resultfile_text, outpath_result, maplist,
                all_runtime_in_sec, base_www_url, statfile=statfile)

        # now making zip instead (for windows users)
        # note that zip rq will zip the real data for symbolic links
        zipfile = "%s.zip"%(jobid)
        zipfile_fullpath = "%s/%s"%(rstdir, zipfile)
        os.chdir(rstdir)
        cmd = ["zip", "-rq", zipfile, jobid]
        webcom.RunCmd(cmd, runjob_logfile, runjob_errfile)

        date_str = time.strftime(g_params['FORMAT_DATETIME'])
        if len(failed_idx_list)>0:
            myfunc.WriteFile(date_str, failedtagfile, "w", True)

        myfunc.WriteFile(date_str, finishtagfile, "w", True)

        if finish_status == "success":
            shutil.rmtree(tmpdir)


        # send the result to email
        if webcom.IsFrontEndNode(base_www_url) and myfunc.IsValidEmailAddress(email):
            webcom.SendEmail_on_finish(jobid, base_www_url,
                    finish_status, name_server="SCAMPI2", from_email="no-reply.SCAMPI@bioinfo.se",
                    to_email=email, contact_email=contact_email,
                    logfile=runjob_logfile, errfile=runjob_errfile)
        webcom.CleanJobFolder_Scampi(rstdir)

#}}}
def RunStatistics(path_result, path_log):#{{{
# 1. calculate average running time, only for those sequences with time.txt
# show also runtime of type and runtime -vs- seqlength
    myfunc.WriteFile("RunStatistics...\n", gen_logfile, "a", True)
    allfinishedjoblogfile = "%s/all_finished_job.log"%(path_log)
    runtimelogfile = "%s/jobruntime.log"%(path_log)
    runtimelogfile_finishedjobid = "%s/jobruntime_finishedjobid.log"%(path_log)
    allsubmitjoblogfile = "%s/all_submitted_seq.log"%(path_log)
    if not os.path.exists(path_stat):
        os.mkdir(path_stat)

    allfinishedjobidlist = myfunc.ReadIDList2(allfinishedjoblogfile, col=0, delim="\t")
    runtime_finishedjobidlist = myfunc.ReadIDList(runtimelogfile_finishedjobid)
    toana_jobidlist = list(set(allfinishedjobidlist)-set(runtime_finishedjobidlist))

    for jobid in toana_jobidlist:
        runtimeloginfolist = []
        rstdir = "%s/%s"%(path_result, jobid)
        outpath_result = "%s/%s"%(rstdir, jobid)
        finished_seq_file = "%s/finished_seqs.txt"%(outpath_result)
        lines = []
        if os.path.exists(finished_seq_file):
            lines = myfunc.ReadFile(finished_seq_file).split("\n")
        for line in lines:
            strs = line.split("\t")
            if len(strs)>=7:
                str_seqlen = strs[1]
                str_loc_def = strs[2]
                str_loc_def_score = strs[3]
                source = strs[4]
                if source == "newrun":
                    subfolder = strs[0]
                    timefile = "%s/%s/%s"%(outpath_result, subfolder, "time.txt")
                    if os.path.exists(timefile) and os.path.getsize(timefile)>0:
                        txt = myfunc.ReadFile(timefile).strip()
                        try:
                            ss2 = txt.split(";")
                            runtime_str = ss2[1]
                            database_mode = ss2[2]
                            runtimeloginfolist.append("\t".join([jobid, subfolder,
                                source, runtime_str, database_mode, str_seqlen,
                                str_loc_def, str_loc_def_score]))
                        except:
                            sys.stderr.write("bad timefile %s\n"%(timefile))

        if len(runtimeloginfolist)>0:
            # items 
            # jobid, seq_no, newrun_or_cached, runtime, mtd_profile, seqlen, numTM, iShasSP
            myfunc.WriteFile("\n".join(runtimeloginfolist)+"\n",runtimelogfile, "a", True)
        myfunc.WriteFile(jobid+"\n", runtimelogfile_finishedjobid, "a", True)

#2. get numseq_in_job vs count_of_jobs, logscale in x-axis
#   get numseq_in_job vs waiting time (time_start - time_submit)
#   get numseq_in_job vs finish time  (time_finish - time_submit)

    allfinished_job_dict = myfunc.ReadFinishedJobLog(allfinishedjoblogfile)
    countjob_country = {} # countjob_country['country'] = [numseq, numjob, ip_set]
    outfile_numseqjob = "%s/numseq_of_job.stat.txt"%(path_stat)
    outfile_numseqjob_web = "%s/numseq_of_job.web.stat.txt"%(path_stat)
    outfile_numseqjob_wsdl = "%s/numseq_of_job.wsdl.stat.txt"%(path_stat)
    countjob_numseq_dict = {} # count the number jobs for each numseq
    countjob_numseq_dict_web = {} # count the number jobs for each numseq submitted via web
    countjob_numseq_dict_wsdl = {} # count the number jobs for each numseq submitted via wsdl

    waittime_numseq_dict = {}
    waittime_numseq_dict_web = {}
    waittime_numseq_dict_wsdl = {}

    finishtime_numseq_dict = {}
    finishtime_numseq_dict_web = {}
    finishtime_numseq_dict_wsdl = {}

    for jobid in allfinished_job_dict:
        li = allfinished_job_dict[jobid]
        numseq = -1
        try:
            numseq = int(li[4])
        except:
            pass
        try:
            method_submission = li[5]
        except:
            method_submission = ""

        ip = ""
        try:
            ip = li[2]
        except:
            pass

        country = "N/A"           # this is slow
        try:
            match = geolite2.lookup(ip)
            country = pycountry.countries.get(alpha_2=match.country).name
        except:
            pass
        if country != "N/A":
            if not country in countjob_country:
                countjob_country[country] = [0,0,set([])] #[numseq, numjob, ip_set] 
            if numseq != -1:
                countjob_country[country][0] += numseq
            countjob_country[country][1] += 1
            countjob_country[country][2].add(ip)


        submit_date_str = li[6]
        start_date_str = li[7]
        finish_date_str = li[8]

        if numseq != -1:
            if not numseq in  countjob_numseq_dict:
                countjob_numseq_dict[numseq] = 0
            countjob_numseq_dict[numseq] += 1
            if method_submission == "web":
                if not numseq in  countjob_numseq_dict_web:
                    countjob_numseq_dict_web[numseq] = 0
                countjob_numseq_dict_web[numseq] += 1
            if method_submission == "wsdl":
                if not numseq in  countjob_numseq_dict_wsdl:
                    countjob_numseq_dict_wsdl[numseq] = 0
                countjob_numseq_dict_wsdl[numseq] += 1

#           # calculate waittime and finishtime
            isValidSubmitDate = True
            isValidStartDate = True
            isValidFinishDate = True
            try:
                submit_date = webcom.datetime_str_to_time(submit_date_str)
            except ValueError:
                isValidSubmitDate = False
            try:
                start_date =  webcom.datetime_str_to_time(start_date_str)
            except ValueError:
                isValidStartDate = False
            try:
                finish_date = webcom.datetime_str_to_time(finish_date_str)
            except ValueError:
                isValidFinishDate = False

            if isValidSubmitDate and isValidStartDate:
                waittime_sec = (start_date - submit_date).total_seconds()
                if not numseq in waittime_numseq_dict:
                    waittime_numseq_dict[numseq] = []
                waittime_numseq_dict[numseq].append(waittime_sec)
                if method_submission == "web":
                    if not numseq in waittime_numseq_dict_web:
                        waittime_numseq_dict_web[numseq] = []
                    waittime_numseq_dict_web[numseq].append(waittime_sec)
                if method_submission == "wsdl":
                    if not numseq in waittime_numseq_dict_wsdl:
                        waittime_numseq_dict_wsdl[numseq] = []
                    waittime_numseq_dict_wsdl[numseq].append(waittime_sec)
            if isValidSubmitDate and isValidFinishDate:
                finishtime_sec = (finish_date - submit_date).total_seconds()
                if not numseq in finishtime_numseq_dict:
                    finishtime_numseq_dict[numseq] = []
                finishtime_numseq_dict[numseq].append(finishtime_sec)
                if method_submission == "web":
                    if not numseq in finishtime_numseq_dict_web:
                        finishtime_numseq_dict_web[numseq] = []
                    finishtime_numseq_dict_web[numseq].append(finishtime_sec)
                if method_submission == "wsdl":
                    if not numseq in finishtime_numseq_dict_wsdl:
                        finishtime_numseq_dict_wsdl[numseq] = []
                    finishtime_numseq_dict_wsdl[numseq].append(finishtime_sec)


    # output countjob by country
    outfile_countjob_by_country = "%s/countjob_by_country.txt"%(path_stat)
    # sort by numseq in descending order
    li_countjob = sorted(list(countjob_country.items()), key=lambda x:x[1][0], reverse=True) 
    li_str = []
    li_str.append("#Country\tNumSeq\tNumJob\tNumIP")
    for li in li_countjob:
        li_str.append("%s\t%d\t%d\t%d"%(li[0], li[1][0], li[1][1], len(li[1][2])))
    myfunc.WriteFile(("\n".join(li_str)+"\n").encode('utf-8'), outfile_countjob_by_country, "wb", True)

    flist = [outfile_numseqjob, outfile_numseqjob_web, outfile_numseqjob_wsdl  ]
    dictlist = [countjob_numseq_dict, countjob_numseq_dict_web, countjob_numseq_dict_wsdl]
    for i in range(len(flist)):
        dt = dictlist[i]
        outfile = flist[i]
        sortedlist = sorted(list(dt.items()), key = lambda x:x[0])
        if os.path.getsize(outfile) > 0:
            try:
                fpout = open(outfile,"w")
                for j in range(len(sortedlist)):
                    nseq = sortedlist[j][0]
                    count = sortedlist[j][1]
                    fpout.write("%d\t%d\n"%(nseq,count))
                fpout.close()
                cmd = ["%s/app/plot_numseq_of_job.sh"%(basedir), outfile]
                webcom.RunCmd(cmd, gen_logfile, gen_errfile)
            except IOError:
                continue
    if os.path.getsize(outfile_numseqjob_wsdl) > 0:
        cmd = ["%s/app/plot_numseq_of_job_mtp.sh"%(basedir), "-web",
                outfile_numseqjob_web, "-wsdl", outfile_numseqjob_wsdl]
        webcom.RunCmd(cmd, gen_logfile, gen_errfile)

#}}}

def main(g_params):#{{{
    submitjoblogfile = "%s/submitted_seq.log"%(path_log)
    runjoblogfile = "%s/runjob_log.log"%(path_log)
    finishedjoblogfile = "%s/finished_job.log"%(path_log)

    if not os.path.exists(path_cache):
        os.mkdir(path_cache)

    loop = 0
    while 1:
        base_www_url_file = "%s/static/log/base_www_url.txt"%(basedir)
        base_www_url = myfunc.ReadFile(base_www_url_file).strip()

        # load the config file if exists
        configfile = "%s/config/config.json"%(basedir)
        config = {}
        if os.path.exists(configfile):
            text = myfunc.ReadFile(configfile)
            config = json.loads(text)

        if rootname_progname in config:
            g_params.update(config[rootname_progname])

        if os.path.exists(black_iplist_file):
            g_params['blackiplist'] = myfunc.ReadIDList(black_iplist_file)

        date_str = time.strftime(g_params['FORMAT_DATETIME'])
        avail_computenode = webcom.ReadComputeNode(computenodefile) # return value is a dict
        num_avail_node = len(avail_computenode)
        webcom.loginfo("loop %d"%(loop), gen_logfile)

        CreateRunJoblog(path_result, submitjoblogfile, runjoblogfile,
                finishedjoblogfile, loop)

        # Get number of jobs submitted to the remote server based on the
        # runjoblogfile
        runjobidlist = myfunc.ReadIDList2(runjoblogfile,0)
        remotequeueDict = {}
        for node in avail_computenode:
            remotequeueDict[node] = []
        for jobid in runjobidlist:
            rstdir = "%s/%s"%(path_result, jobid)
            remotequeue_idx_file = "%s/remotequeue_seqindex.txt"%(rstdir)
            if os.path.exists(remotequeue_idx_file):
                content = myfunc.ReadFile(remotequeue_idx_file)
                lines = content.split('\n')
                for line in lines:
                    strs = line.split('\t')
                    if len(strs)>=5:
                        node = strs[1]
                        remotejobid = strs[2]
                        if node in remotequeueDict:
                            remotequeueDict[node].append(remotejobid)


        if loop % g_params['STATUS_UPDATE_FREQUENCY'][0] == g_params['STATUS_UPDATE_FREQUENCY'][1]:
            RunStatistics(path_result, path_log)
            webcom.DeleteOldResult(path_result, path_log, gen_logfile, MAX_KEEP_DAYS=g_params['MAX_KEEP_DAYS'])
            webcom.CleanServerFile(path_static, gen_logfile, gen_errfile)
        webcom.ArchiveLogFile(path_log, threshold_logfilesize=threshold_logfilesize) 

        cntSubmitJobDict = webcom.InitCounterSubmitJobDict(avail_computenode, remotequeueDict, g_params['MAX_SUBMIT_JOB_PER_NODE'])

# entries in runjoblogfile includes jobs in queue or running
        hdl = myfunc.ReadLineByBlock(runjoblogfile)
        if not hdl.failure:
            lines = hdl.readlines()
            while lines != None:
                for line in lines:
                    strs = line.split("\t")
                    if len(strs) >= 11:
                        jobid = strs[0]
                        client_ip = strs[3]
                        email = strs[4]
                        try:
                            numseq = int(strs[5])
                        except:
                            numseq = 1
                            pass
                        try:
                            app_type = strs[10]
                        except:
                            app_type = 'None'
                        try:
                            numseq_this_user = int(strs[11])
                        except:
                            numseq_this_user = 1
                            pass
                        rstdir = "%s/%s"%(path_result, jobid)
                        forceruntagfile = "%s/forcerun"%(rstdir)
                        finishtagfile = "%s/%s"%(rstdir, "runjob.finish")
                        status = strs[1]
                        webcom.loginfo("CompNodeStatus: %s"%(str(cntSubmitJobDict)), gen_logfile)
                        runjob_lockfile = "%s/%s/%s.lock"%(path_result, jobid, "runjob.lock")
                        if os.path.exists(runjob_lockfile):
                            msg = "runjob_lockfile %s exists, ignore the job %s" %(runjob_lockfile, jobid)
                            date_str = time.strftime(g_params['FORMAT_DATETIME'])
                            myfunc.WriteFile("[%s] %s\n"%(date_str, msg), gen_logfile, "a", True)
                            continue

                        if app_type == "SCAMPI-single":
                            query = {}
                            query['jobid'] = jobid
                            query['numseq'] = numseq
                            query['numseq_this_user'] = numseq_this_user
                            query['base_www_url'] = base_www_url
                            query['email'] = email
                            query['client_ip'] = client_ip
                            query['app_type'] = app_type
                            if os.path.exists(forceruntagfile):
                                query['isForceRun'] = True
                            else:
                                query['isForceRun'] = False
                            tmpdir = os.path.join(rstdir, "tmp1")
                            if not os.path.exists(tmpdir):
                                os.makedirs(tmpdir)
                            webcom.SubmitQueryToLocalQueue(query, tmpdir, rstdir, g_params, isOnlyGetCache=False)

                        if webcom.IsHaveAvailNode(cntSubmitJobDict):
                            if not g_params['DEBUG_NO_SUBMIT']:
                                SubmitJob(jobid, cntSubmitJobDict, numseq_this_user)
                        GetResult(jobid) # the start tagfile is written when got the first result
                        CheckIfJobFinished(jobid, numseq, email)

                lines = hdl.readlines()
            hdl.close()

        webcom.loginfo("sleep for %d seconds"%(g_params['SLEEP_INTERVAL']), gen_logfile)
        time.sleep(g_params['SLEEP_INTERVAL'])
        loop += 1

    return 0
#}}}


def InitGlobalParameter():#{{{
    g_params = {}
    g_params['isQuiet'] = True
    g_params['blackiplist'] = []
    g_params['DEBUG'] = False
    g_params['DEBUG_NO_SUBMIT'] = False
    g_params['DEBUG_CACHE'] = False
    g_params['SLEEP_INTERVAL'] = 5    # sleep interval in seconds
    g_params['MAX_SUBMIT_JOB_PER_NODE'] = 200
    g_params['MAX_TIME_IN_REMOTE_QUEUE'] = 3600*24 # one day in seconds
    g_params['MAX_KEEP_DAYS'] = 60
    g_params['MAX_RESUBMIT'] = 2
    g_params['TZ'] = "Europe/Stockholm"
    g_params['FORMAT_DATETIME'] = webcom.FORMAT_DATETIME
    g_params['STATUS_UPDATE_FREQUENCY'] = [500, 50]  # updated by if loop%$1 == $2
    g_params['path_result'] = path_result
    g_params['path_static'] = path_static
    g_params['SITE_ROOT'] = basedir
    g_params['gen_logfile'] = gen_logfile
    g_params['gen_errfile'] = gen_errfile
    g_params['path_cache'] = path_cache
    return g_params
#}}}
if __name__ == '__main__' :
    g_params = InitGlobalParameter()
    date_str = time.strftime(g_params['FORMAT_DATETIME'])
    print("\n#%s#\n[Date: %s] qd_fe.py restarted"%('='*80,date_str))
    sys.stdout.flush()
    sys.exit(main(g_params))
