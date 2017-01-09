#!/usr/bin/python3

import glob
import os
import subprocess
import sys
import locale

encoding = locale.getdefaultlocale()[1]

path = '/home/chanhle/hg/si2/tinf/tpdb/C/Ultimate'
hip = '/home/chanhle/hg/si2/hip'
os.chdir(path)

error = []

filelist = glob.glob('*.c')

for file in sorted(filelist):
  sys.stdout.write(file + ': ')
  sys.stdout.flush()
  p = subprocess.Popen([hip, '-infer', '"@term"', file], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  try:
    outs, errs = p.communicate(timeout=10)
    out = outs.decode(encoding)
    if 'Error' in out:
      print('Error')
    elif 'FAIL' in out:
      print('Fail')
    elif 'MayLoop' in out:
      print('MayLoop')
    else:
      print('Ok')
  except subprocess.TimeoutExpired:
    p.kill()
    outs, errs = p.communicate()
    print('Timeout')
