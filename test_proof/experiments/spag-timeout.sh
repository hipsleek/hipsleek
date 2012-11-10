#!/bin/bash

# Usage: ./spag.sh n prover timeout

HOME=/home/chanhle/hg/proof_logging/sleekex
SLEEK=$HOME/sleek
SPAG=$HOME/slice/examples/working_examples/asankhs_benchmarks

SLK_TIMEOUT=$3

LOG=logs_$(date +%b%d_%H%M)
echo $LOG
mkdir $LOG

for ((i = 10; i <= $1; i++))
do
	# No caching
	echo "spaguetti-$i"
	./kill $2
	(time $SLEEK -tp $2 --dis-provers-timeout --sleek-timeout $3 $SPAG/spaguetti-$i.slk) >$LOG/spaguetti.$2.$1 2>&1
	(time $SLEEK -tp $2 --dis-provers-timeout --sleek-timeout $3 $SPAG/spaguetti-$i.slk --eps --efp --enable-slicing) >$LOG/spaguetti.efp.aus.$2.$1 2>&1
	(time $SLEEK -tp $2 --dis-provers-timeout --sleek-timeout $3 $SPAG/spaguetti-$i.slk --eps --efp --enable-slicing --slc-ann-ineq) >$LOG/spaguetti.efp.ans.$2.$1 2>&1

	# Caching
	(time $SLEEK -tp $2 --dis-provers-timeout --sleek-timeout $3 --enable-cache $SPAG/spaguetti-$i.slk --eps --efp --enable-slicing --slc-ann-ineq) >$LOG/spaguetti.efp.ans.$2.$1c 2>&1
done

./kill $2
