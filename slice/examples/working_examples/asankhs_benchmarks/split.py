#!/usr/bin/python

import sys
import os
import subprocess
import time

sleek_exec = '/home/chanhle/hg/slicing/sleekex/sleek'
eps_flag = '--eps'
slicing_flag = '--enable-slicing'
ineq_flag = '--slc-opt-ineq'
ufdp_flag = '--ufdp'

def split_and_run (filename, fileext):
    i = 1
    header = "data node { int val ; node next }." + "\n\n" + "pred lseg<p> == self = p" + "\n" + "or self::node<_,r> * r::lseg<p> & self!=p inv true." + "\n\n"
    infile = open(filename + '.' + fileext, 'r')
    resfile = open(filename + '.res', 'w')
    for line in infile:
	if line.startswith('checkentail'):
	    fname = filename + '-' + str(i) + '.' + fileext
			
	    outfile = open(fname, 'w')
	    outfile.write(header + line)
	    outfile.close()

	    args = []
	    args.append(sleek_exec)
	    args.append(eps_flag)
	    args.append(slicing_flag)
            args.append(ufdp_flag)
            args.append(ineq_flag)
	    args.append(fname)

            start_time = time.time()
	    process = subprocess.Popen(args, shell=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

            """
            timeout = 300
            start_time = time.time()
            elapsed_time = 0
            
            #Approximate runtime of process
            while process.poll() is None and elapsed_time < timeout:
                elapsed_time = time.time() - start_time
            """

            #communicate waits for process to terminate
	    stdout, stderr = process.communicate()
            elapsed_time = time.time() - start_time

        if stdout.find('Fail') != -1:
			res = 'F'
	    else:
			res = 'S'

	    resfile.write(str(i) + "\t" + str(elapsed_time) + "\t" + res + "\n")
	    i = i + 1
    infile.close()
    resfile.close()

def main():
    split_and_run (sys.argv[1], 'slk')

main()
		
