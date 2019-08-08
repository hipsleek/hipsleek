#!/usr/bin/env python2

# Usage: ./run-benchmark.py directory-name
# e.g. ./run-benchmark.py examples/working/hip/repair/benchmark/


import os
import time
import sys
import subprocess
import argparse
import datetime
import signal
import psutil
from threading import Timer
from glob import glob

# prepare environments
os.environ["LC_ALL"] = "C"
script_dir = sys.path[0]
current_dir = os.getcwd()
home_dir = os.path.realpath(script_dir)
timeout = 50

# parse arguments
def parse_args ():
    parser = argparse.ArgumentParser(description='Run benchmark')
    parser.add_argument('benchmark', help='Path to the benchmark')
    parser.add_argument('--options', dest='options', default='',
                        help='Options for Songbird')
    parser.add_argument('--log', dest='log_file', default='',
                        help='Log file to capture output')
    parser.add_argument('--timeout', dest='timeout', type=int, default=0,
                        help='Timeout for each test case')
    args = parser.parse_args()
    return args


# global vars
total_valid = 0
total_invalid = 0
total_unknown = 0
total_timeout = 0

# report error and quit
def error(msg):
    print("Error: " + msg);
    sys.exit (1);

# Finding execution file of HIP
def find_hip_path():
    hip_byte = home_dir + "/" + "hip"
    if os.path.isfile(hip_byte):
        return hip_byte
    else:
        error ("Looking for '" + hip_byte + "' but not found");

def find_test_cases(testcase_dir):
    files = [y
             for x in os.walk(testcase_dir)
             for y in glob(os.path.join(x[0], '*.ss'))]
    files = sorted(files)
    return files

def get_status(output):
    output_success = "REPAIRING SUCCESSFUL"
    output_fail = "REPAIRING FAIL"
    if output_success in output:
        return "Success"
    elif output_fail in output:
        return "Fail"
    else:
        return "Unknown"

def write_to_file(log_file, msg):
    if log_file:
        file = open(log_file, "a+")
        file.write(msg + "\n")
        file.close()

def kill_process(process):
    process.kill()
    os.killpg(os.getpgid(process.pid), signal.SIGTERM)   # kill sub-processes

# run HIP, pass options as a list of options
def run_hip(hip, benchmark, log_file):
    global total_valid, total_invalid, total_unknown, total_timeout
    testcase_dir = current_dir + "/" + benchmark
    options = ["--en-repair"]
    for testcase in find_test_cases(testcase_dir):
        time_begin = time.time()
        prover = subprocess.Popen([hip, testcase] + options,
                                  stdout = subprocess.PIPE,
                                  stderr = subprocess.PIPE,
                                  preexec_fn=os.setsid)
        my_timer = Timer(timeout, kill_process, [prover])

        try:
            my_timer.start()
            stdout, stderr = prover.communicate()
            status = get_status(stdout)
        except Exception:
            status = "Timeout"
        finally:
            my_timer.cancel()

        if status == "Success":
            total_valid = total_valid + 1
        elif status == "Fail":
            total_invalid = total_invalid + 1
        elif status == "Timeout":
            total_timeout = total_timeout + 1
        else:
            total_unknown = total_unknown + 1

        # report result
        time_end = time.time()
        runtime = time_end - time_begin
        runtime = float("{0:.3f}".format(runtime))
        runtime = str(runtime)
        testcase_name = os.path.relpath(testcase, testcase_dir)
        result = testcase_name + "\t" + status + "\t" + runtime
        print(result)
        for proc in psutil.process_iter():
            if proc.name() == "oc" or proc.name() == "z3":
                proc.kill()
        # p = subprocess.Popen(['ps', '-A'], stdout=subprocess.PIPE)
        # out, err = p.communicate()
        # for line in out.splitlines():
        #     if 'oc' in line:
        #         pid = int(line.split(None, 1)[0])
        #         os.kill(pid, signal.SIGKILL)

        # write_to_file(log_file, result)


# main function
def main():
    global total_valid, total_invalid, total_unknown, total_timeout, timeout

    # parse input
    args = parse_args ()
    benchmark = args.benchmark
    options = args.options.split()
    log_file = args.log_file
    if (args.timeout > 0):
        timeout = args.timeout

    # prepare environments
    hip = find_hip_path()
    msg = ("====================================\n" +
           "TESTING FIXHEAP..." + "\n\n" +
           "Prover: " + hip + "\n" +
           "Benchmark: " + benchmark + "\n" +
           "Timeout: " + str(timeout) + "s\n")
    if options:
        msg = msg + "Options: " + str(options) + "\n"
    if log_file:
        msg = msg + "Log file: " + log_file + "\n"
    now = datetime.datetime.now()
    msg = msg + "Date: " + now.strftime("%Y-%m-%d %H:%M:%S") + "\n"

    print(msg)
    if log_file and os.path.exists(log_file):
        os.remove(log_file)
    # write_to_file(log_file, msg)

    # init vars
    total_valid = 0; total_invalid = 0; total_unknown = 0; total_timeout = 0
    time_begin = time.time()

    run_hip(hip, benchmark, log_file)

    # statistics
    time_end = time.time()
    total_time = time_end - time_begin
    msg = ("\nSummary: " + str(total_valid) + " success, " +
           str(total_invalid) + " failed, " +
           str(total_unknown) + " timeout, " +
           # str(total_timeout) + " timeout\n" +
           "Time: " + "{:0.2f}".format(total_time) + "s\n")
    print(msg)
    # write_to_file(log_file, msg)

# run main
main()
