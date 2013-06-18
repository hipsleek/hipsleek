#!/usr/bin/python
import subprocess
import sys
import os
import getopt


SIZE_LIMIT = 1048576 # commit files of max 1MB, otherwise warn the user
#number of files limit: 
NOF_LIMIT = 10 # commit max 10 modified files without warning the user 


temp_file = "commit_temp"
log_message = "x" # default commit message
commit_command = "hg commit -m \"" + log_message + "\"" # the commit command
nof = 0 #number of modified/added files
size_warning = False
force_verif  = False 

# parse command line arguments
opts, args = getopt.getopt(sys.argv[1:],"hv",[])
for opt, arg in opts:
    if opt == '-h':
        print './hgcommit.py [-v] [<commit message>] '
    elif opt == '-v':
        force_verif = True

if len(args) > 0 :
    log_message = args[0]


#check for modified files (size of modified files does not produce any warning)
print "Checking hg stat for added/modified files... "
subprocess.call("hg stat -mn  > " + temp_file, executable="bash", shell=True)

f = open(temp_file, 'r+')
for line in f:
    nof += 1
    print "M " + line.rstrip('\n')
    # don't check modified files for size
    # b = os.path.getsize(line.rstrip('\n'))
    # if (b > SIZE_LIMIT):
    #     size_warning = True


#check for added files
subprocess.call("hg stat -an  > " + temp_file, executable="bash", shell=True)
f = open(temp_file, 'r+')
for line in f:
    nof += 1
    b = os.path.getsize(line.rstrip('\n'))
    print "A " + line.rstrip('\n') + " (" + str(b) + " bytes)"
    if (b > SIZE_LIMIT):
        size_warning = True


answ = "Continue"
question = "Are you sure you want to continue with this commit? (Continue/no)"


if (nof >= NOF_LIMIT):
    answ = raw_input ("WARNING: Trying to commit more than " + str(nof) +  " files.\n" + question)
elif (size_warning):
    answ = raw_input ("WARNING: Trying to commit files larger than 1 MB. \n" + question)
elif (force_verif):
    answ = raw_input (question)


if answ == "Continue":
    subprocess.call( commit_command, executable="bash", shell=True)
else:
    print "Commit aborted"


subprocess.call("rm " + temp_file, executable="bash", shell=True)
