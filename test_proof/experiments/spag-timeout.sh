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
	echo "  No Slicing"
	(time $SLEEK -tp $2 --dis-provers-timeout --sleek-timeout $3 $SPAG/spaguetti-$i.slk) >$LOG/spaguetti.$i.$2 2>&1
	./kill $2
	echo "  No Slicing (eps)"
	(time $SLEEK -tp $2 --dis-provers-timeout --sleek-timeout $3 $SPAG/spaguetti-$i.slk --eps --efp --force-one-slice) >$LOG/spaguetti.efp.ns.$i.$2 2>&1
	./kill $2
	echo "  Auto Slicing"
	(time $SLEEK -tp $2 --dis-provers-timeout --sleek-timeout $3 $SPAG/spaguetti-$i.slk --eps --efp --en-slicing) >$LOG/spaguetti.efp.aus.$i.$2 2>&1
	./kill $2
	echo "  Anno Slicing"
	(time $SLEEK -tp $2 --dis-provers-timeout --sleek-timeout $3 $SPAG/spaguetti-$i.slk --eps --efp --en-slicing --slc-ann-ineq) >$LOG/spaguetti.efp.ans.$i.$2 2>&1

	# Caching
	./kill $2
	echo "  No Slicing (caching)"
	(time $SLEEK -tp $2 --dis-provers-timeout --sleek-timeout $3 --en-cache $SPAG/spaguetti-$i.slk) >$LOG/spaguetti.$i.$2c 2>&1
	./kill $2
	echo "  No Slicing (eps) (caching)"
	(time $SLEEK -tp $2 --dis-provers-timeout --sleek-timeout $3 --en-cache $SPAG/spaguetti-$i.slk --eps --efp --force-one-slice) >$LOG/spaguetti.efp.ns.$i.$2c 2>&1
	./kill $2
	echo "  Auto Slicing (caching)"
	(time $SLEEK -tp $2 --dis-provers-timeout --sleek-timeout $3 --en-cache $SPAG/spaguetti-$i.slk --eps --efp --en-slicing) >$LOG/spaguetti.efp.aus.$i.$2c 2>&1
	./kill $2
	echo "  Anno Slicing (caching)"
	(time $SLEEK -tp $2 --dis-provers-timeout --sleek-timeout $3 --en-cache $SPAG/spaguetti-$i.slk --eps --efp --en-slicing --slc-ann-ineq) >$LOG/spaguetti.efp.ans.$i.$2c 2>&1
done

./kill $2
