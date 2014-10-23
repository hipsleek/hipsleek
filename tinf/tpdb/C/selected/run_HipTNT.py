#!/usr/bin/python3.4

import glob
import os
import subprocess
import sys
import locale
import re
import argparse

encoding = locale.getdefaultlocale()[1]

path = '/home/chanhle/hg/si2/tinf/tpdb/C/selected/'
hip = '/home/chanhle/hg/si2/hip'

infer_lex = [
  '4BitCounterPointer_true-termination.c',
  '4BitCounter_true-termination.c',
  'LexIndexValue-Pointer_true-termination.c',
  'Nyala-2lex_true-termination.c',
  'svcomp_Ackermann01_true-unreach-call_modified_modified.c'
]

parser = argparse.ArgumentParser(description='To run the script with options')
parser.add_argument('-b', action="store", dest="bench")
results = parser.parse_args()

# for bench in (os.walk(path).__next__()[1]):
bench = results.bench
print(bench)
spath = path + bench
os.chdir(spath)
filelist = glob.glob('*.c')

os.system("export C_INCLUDE_PATH=.")

for file in sorted(filelist):
  filename = os.path.basename(file)
  sys.stdout.write(filename + '\t')
  sys.stdout.flush()
  t1 = os.times()
  if filename in infer_lex:
    p = subprocess.Popen([hip, '-infer', '"@term"', '--infer-lex', file], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  else:
    p = subprocess.Popen([hip, '-infer', '"@term"', file], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  try:
    outs, errs = p.communicate(timeout=300)
    t2 = os.times()
    proc_time = (t2.children_user - t1.children_user) + (t2.children_system - t1.children_system)
    real_time = t2.elapsed - t1.elapsed
    out = outs.decode(encoding)

    runtime_hip = ""
    for line in out.split("\n"):
      if "Total verification time:" in line:
        runtime_hip = re.findall("\d+.\d+", line)[0]
     
    if 'Error' in out:
      out = 'Error'
    elif 'FAIL' in out:
      out = 'Fail'
    elif 'MayLoop' in out:
      out = 'MayLoop'
    else:
      out = 'Ok'
    print((out + '\t{0:.2f}' + '\t{1:.2f}' + '\t{2}').format(proc_time, real_time, runtime_hip))
  except subprocess.TimeoutExpired:
    p.kill()
    outs, errs = p.communicate()
    print('Timeout')




