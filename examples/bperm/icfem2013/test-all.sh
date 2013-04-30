#!/bin/bash

HOME=/home/khanh/hg/para5-barrier/sleekex
SLEEK=$HOME/sleek
HIP=$HOME/hip
EXPERIMENT=$HOME/bperm/experiment/benchmarks

rm test-all.res

for prog in $( ls *.ss ); do
	echo "============================="
	echo "===$prog"
	echo "============================="
	echo "===$prog===" >> test.res
    $HIP $prog | grep -E 'Proc|assert' >> test-all.res
done

