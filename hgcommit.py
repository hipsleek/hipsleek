#!/usr/bin/python
import subprocess
import sys
import os
import getopt


SIZE_LIMIT = 1048576 # commit files of max 1MB, otherwise warn the user
NOF_LIMIT = 10 # number of files limit: commit max NOF_LIMIT modified/added/deleted files without warning the user 


temp_file = "commit_temp"
log_message = "" 
nof = 0 #number of modified/added files
size_warning = False
force_verif  = False
commit_usage =  'usage: ./commit [-v] -m <commit message> '

# parse command line arguments
try:
    opts, args = getopt.getopt(sys.argv[1:],"hvm:",[])
    for opt, arg in opts:
        if opt == '-h':
            print commit_usage
            sys.exit(2)
        elif opt == '-v':
            force_verif = True
        elif opt == "-m":
            log_message = arg
except getopt.GetoptError as e:
    print (str(e))
    print commit_usage
    sys.exit(2)

if len(log_message) <= 0 :
    print "Insufficient commit arguments: non-empty commit message mandatory \n" + commit_usage
    sys.exit(2)

commit_command = "hg commit -m \"" + log_message + "\"" # the commit command

#check for modified files (size of modified files does not produce any warning)
print "Checking hg stat for added/modified/deleted files... "
subprocess.call("hg stat -mn  > " + temp_file, executable="bash", shell=True)

f = open(temp_file, 'r+')
for line in f:
    nof += 1
    b = os.path.getsize(line.rstrip('\n'))
    if (b > SIZE_LIMIT):
        print "M " + line.rstrip('\n') + " (" + str(b) + " bytes)"
        size_warning = True
    else:
        print "M " + line.rstrip('\n')


#check for added files
subprocess.call("hg stat -an  > " + temp_file, executable="bash", shell=True)
f = open(temp_file, 'r+')
for line in f:
    nof += 1
    b = os.path.getsize(line.rstrip('\n'))
    print "A " + line.rstrip('\n') + " (" + str(b) + " bytes)"
    if (b > SIZE_LIMIT):
        size_warning = True

#check for removed files
subprocess.call("hg stat -rn  > " + temp_file, executable="bash", shell=True)
f = open(temp_file, 'r+')
for line in f:
    nof += 1
    print "R " + line.rstrip('\n')

#check for deleted files
subprocess.call("hg stat -dn  > " + temp_file, executable="bash", shell=True)
f = open(temp_file, 'r+')
for line in f:
    nof += 1
    print "D " + line.rstrip('\n')

answ = "Continue"
question = "Are you sure you want to continue with this commit? (Continue/no)"

if (nof == 0):
    print "Nothing changed"
    answ = "no"
elif (nof >= NOF_LIMIT):
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
