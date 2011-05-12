#!/usr/bin/env python
# indent your Python code to put into an email
import glob
import subprocess
# glob supports Unix style pathname extensions
python_files = glob.glob('*.ml')
for fn in sorted(python_files):
    subprocess.call("wc "+fn,shell=True)
#   print '    ------', fn
#    for line in open(fn):
#        print '    ' + line.rstrip()
#    print
#subprocess.call("ls -l *.ml",shell=True)
