#!/usr/bin/python3.4

import glob
import os
import subprocess
import sys
import locale
import re

encoding = locale.getdefaultlocale()[1]

path = '/home/chanhle/hg/si2/tinf/tpdb/C/AProVE_numeric'
hip = '/home/chanhle/hg/si2/hip'

os.chdir(path)
filelist = glob.glob('*.c')

for file in sorted(filelist):
  sys.stdout.write(os.path.basename(file) + '\t')
  sys.stdout.flush()
  t1 = os.times()
  p = subprocess.Popen([hip, '-infer', '"@term"', file], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  try:
    outs, errs = p.communicate(timeout=300)
    t2 = os.times()
    runtime = (t2.children_user - t1.children_user) + (t2.children_system - t1.children_system)
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
    print((out + '\t{0:.5f}' + '\t{1}').format(runtime, runtime_hip))
  except subprocess.TimeoutExpired:
    p.kill()
    outs, errs = p.communicate()
    print('Timeout')
