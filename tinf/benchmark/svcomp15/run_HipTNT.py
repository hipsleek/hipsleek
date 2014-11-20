#!/usr/bin/python3.4

import glob
import os
import subprocess
import sys
import locale
import re
import argparse

encoding = locale.getdefaultlocale()[1]

path = '/home/chanhle/hg/main/tinf/benchmark/svcomp15/'
hip = '/home/chanhle/hg/main/hip'
hip_sv = '/home/chanhle/hg/main/tinf/benchmark/svcomp15/hiptnt/svcomp15/hiptnt_sv'

infer_lex = [
  # termination-crafted-lit
  'AliasDarteFeautrierGonnord-SAS2010-cousot9_true-termination.c',
  'AliasDarteFeautrierGonnord-SAS2010-Fig1_true-termination.c',
  'AliasDarteFeautrierGonnord-SAS2010-rsd_true-termination.c',
  'AliasDarteFeautrierGonnord-SAS2010-speedpldi3_true-termination.c',
  'CookSeeZuleger-TACAS2013-Fig1_true-termination.c',
  'CookSeeZuleger-TACAS2013-Fig7a_true-termination.c',
  'CookSeeZuleger-TACAS2013-Fig7b_true-termination.c',
  'HarrisLalNoriRajamani-SAS2010-Fig1_true-termination.c',
  'LeeJonesBen-Amram-POPL2001-Ex3_true-termination.c',
  'LeeJonesBen-Amram-POPL2001-Ex4_true-termination.c',
  'PodelskiRybalchenko-TACAS2011-Fig4_true-termination.c',
  'UrbanMine-ESOP2014-Fig3_true-termination.c',
  # termination-numeric
  'Ackermann01_true-termination.c',
  # termination-crafted
  '4BitCounterPointer_true-termination.c',
  '4BitCounter_true-termination.c',
  'LexIndexValue-Pointer_true-termination.c',
  'Nyala-2lex_true-termination.c',
  'svcomp_Ackermann01_true-unreach-call_modified_modified.c',
  # termination-memory-alloca
  'CookSeeZuleger-2013TACAS-Fig3-alloca_true-termination.c',
  'CookSeeZuleger-2013TACAS-Fig7a-alloca_true-termination.c',
  'CookSeeZuleger-2013TACAS-Fig7b-alloca_true-termination.c',
  'HarrisLalNoriRajamani-2010SAS-Fig1-alloca_true-termination.c',
  'Urban-alloca_true-termination.c'
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

for file in sorted(filelist):
  filename = os.path.basename(file)
  sys.stdout.write(filename + '\t')
  sys.stdout.flush()
  #os.system("export C_INCLUDE_PATH=/home/chanhle/hg/main/tinf/benchmark/svcomp15/")
  t1 = os.times()
  if filename in infer_lex:
    #p = subprocess.Popen([hip, '--svcomp-compete', '-infer', '"@shape@term"', '--infer-lex', file], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    p = subprocess.Popen([hip_sv, file], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  else:
    #p = subprocess.Popen([hip, '--svcomp-compete', '-infer', '"@shape@term"', file], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    p = subprocess.Popen([hip_sv, file], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
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
     
    if 'TRUE' in out:
      out = 'TRUE'
    elif 'FALSE' in out:
      out = 'FALSE'
    elif 'UNKNOWN' in out:
      out = 'UNKNOWN'
    else:
      out = 'ERR'
    print((out + '\t{0:.2f}' + '\t{1:.2f}' + '\t{2}').format(proc_time, real_time, runtime_hip))
  except subprocess.TimeoutExpired:
    p.kill()
    outs, errs = p.communicate()
    print('Timeout')




