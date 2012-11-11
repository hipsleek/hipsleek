#!/bin/bash

# Usage: ./spag.sh n prover

HOME=/home/chanhle/hg/proof_logging/sleekex
SLEEK=$HOME/sleek
SPAG=$HOME/slice/examples/working_examples/asankhs_benchmarks

TIMEOUT=300

LOG=logs_$(date +%b%d_%H%M)
echo $LOG
mkdir $LOG

for ((i = 10; i <= $1; i++))
do
	# No caching
	echo "spaguetti-$i"
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 $SPAG/spaguetti-$i.slk)) >$LOG/spaguetti.$2.$i 2>&1
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 $SPAG/spaguetti-$i.slk --eps)) >$LOG/spaguetti.eps.$2.$i 2>&1
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 $SPAG/spaguetti-$i.slk --eps --efp)) >$LOG/spaguetti.efp.$2.$i 2>&1
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 $SPAG/spaguetti-$i.slk --eps --enable-slicing)) >$LOG/spaguetti.eps.aus.$2.$i 2>&1
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 $SPAG/spaguetti-$i.slk --eps --efp --enable-slicing)) >$LOG/spaguetti.efp.aus.$2.$i 2>&1
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 $SPAG/spaguetti-$i.slk --eps --enable-slicing --slc-ann-ineq)) >$LOG/spaguetti.eps.ans.$2.$i 2>&1
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 $SPAG/spaguetti-$i.slk --eps --efp --enable-slicing --slc-ann-ineq)) >$LOG/spaguetti.efp.ans.$2.$i 2>&1

	# Caching
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 --enable-cache $SPAG/spaguetti-$i.slk)) >$LOG/spaguetti.$2.$1c 2>&1
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 --enable-cache $SPAG/spaguetti-$i.slk --eps)) >$LOG/spaguetti.eps.$2.$1c 2>&1
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 --enable-cache $SPAG/spaguetti-$i.slk --eps --efp)) >$LOG/spaguetti.efp.$2.$1c 2>&1
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 --enable-cache $SPAG/spaguetti-$i.slk --eps --enable-slicing)) >$LOG/spaguetti.eps.aus.$2.$1c 2>&1
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 --enable-cache $SPAG/spaguetti-$i.slk --eps --efp --enable-slicing)) >$LOG/spaguetti.efp.aus.$2.$1c 2>&1
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 --enable-cache $SPAG/spaguetti-$i.slk --eps --enable-slicing --slc-ann-ineq)) >$LOG/spaguetti.eps.ans.$2.$1c 2>&1
	(time (./timeout -TERM $TIMEOUT $SLEEK -tp $2 --enable-cache $SPAG/spaguetti-$i.slk --eps --efp --enable-slicing --slc-ann-ineq)) >$LOG/spaguetti.efp.ans.$2.$1c 2>&1
done

./kill $2
