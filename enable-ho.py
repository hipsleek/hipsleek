#!/usr/bin/python
import glob
import subprocess

import os
dirList=glob.glob('*.ml')
to_modify_files = []
temp_file="tmp"

print "Files that need to be modified:"
#check which files have the ho-debugging on
for fname in sorted( dirList):
    subprocess.call("sed -n -f enable-ho-diff.sed " + fname + " > " + temp_file, executable="bash", shell=True)
    b = os.path.getsize(temp_file)
    if b>0 :
        to_modify_files.append(fname)
        print fname

#maybe disable ho-debugging for all the files
no = len(to_modify_files)
if no>0:
    answ = raw_input ("There are a total of " +  str(len(to_modify_files)) + " files to be modified. Do you want to modify them all? (y/n)")
    if answ == "y":
        for fname in sorted(to_modify_files):
            subprocess.call("./enable-ho.sh " + fname, executable="bash", shell=True)
        print ("All files have been modified")
else:
    print "Currently there is no file that has the debugging system deactivated!"
