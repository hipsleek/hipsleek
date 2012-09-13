#!/bin/bash

HIP=/home/chanhle/hg/term_inf/sleekex/hip
TBOUND=10

for f in *.ss;
do
	echo "==================================================";
	echo "Processing $f file ..";
	$HIP --infer-term --tinf-bound $TBOUND $f > tmp;
	diff `echo ${f%.*}`.sol tmp;
	echo "==================================================";
done
