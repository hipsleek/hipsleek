#!/usr/bin/python
import subprocess
import sys
import os

SIZE_LIMIT = 1048576 # commit files of max 1MB, otherwise warn the user
#number of files limit: 
NOF_LIMIT = 10 # commit max 10 modified files without warning the user 

log_message = "x"
if len(sys.argv) > 1 :
    log_message = sys.argv[1]

commit_command = "hg commit -m \"" + log_message + "\""

temp_file="tmp"

print "Checking hg stat for added/modified files... "
subprocess.call("hg stat -man  > " + temp_file, executable="bash", shell=True)
b = os.path.getsize(temp_file)

size_warning = False
#number of files 
nof = 0

f = open(temp_file, 'r+')
for line in f:
    nof += 1
    print line.rstrip('\n')
    b = os.path.getsize(line.rstrip('\n'))
    if (b > SIZE_LIMIT):
        size_warning = True

commit = True
answ = "Continue"

if (nof >= NOF_LIMIT):
    answ = raw_input ("Trying to commit more than " + str(nof) +  " files. Are you sure you want to continue this commit? Continue/no ")
elif (size_warning):
    answ = raw_input ("Trying to commit files larger than 1 MB. Are you sure you want to continue this commit? Continue/no ")

if answ == "Continue":
    subprocess.call( commit_command, executable="bash", shell=True)
else:
    print "Aborting commit to repository..."

