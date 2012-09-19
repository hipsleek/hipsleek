#!/bin/bash

HIP=/home/chanhle/hg/term_inf/sleekex/hip
TBOUND=10

rm result
for f in *.ss;
do
	echo "Processing $f file .."
	
	echo "==================================================" >> result
	echo "Processing $f file .." >> result

	$HIP --infer-term --tinf-bound $TBOUND $f > tmp
	diff `echo ${f%.*}`.sol tmp >> result
	echo "==================================================" >> result
done
