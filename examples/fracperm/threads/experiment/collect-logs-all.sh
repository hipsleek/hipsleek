#!/bin/bash


# Run all tests, output to xls file for experimental comparison
# between threadhip and parahip.
# threadhip: parahip using threads as resource
# parahip: orignal parahip using threads as AND-conj

#HOME=.
HIP=../../../../hip

# Threads as resource
THREADHIP=~/hg/para5-threads/sleekex/examples/fracperm/threads/threadhip
FLAG1="--en-para --en-thrd-resource -tp parahip --en-lsmu-infer"

# Threads as AND-conjunction
PARAHIP=~/hg/para5-threads/sleekex/examples/fracperm/threads/parahip
FLAG2="--en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer"

ITERATIONS=1 # ALWAYS 1

#########################################
#########################################
echo "Running programs in $THREADHIP ..."
for prog in $( ls $THREADHIP/*.ss );
do
    sum=0
    for (( i = 1; i <= $ITERATIONS; i++ ))
    do
	    echo "============================="
	    echo "===$prog : $i"
	    echo "============================="
        $HIP $FLAG1 $prog
    done
done

echo "Running programs in $THREADHIP/parahip-benchmark/ ..."
for prog in $( ls $THREADHIP/parahip-benchmark/*.ss );
do
    sum=0
    for (( i = 1; i <= $ITERATIONS; i++ ))
    do
	    echo "============================="
	    echo "===$prog : $i"
	    echo "============================="
        $HIP $FLAG1 $prog
    done
done

#########################################
#########################################

echo "Running programs in $PARAHIP ..."
for prog in $( ls $PARAHIP/*.ss );
do
    sum=0
    for (( i = 1; i <= $ITERATIONS; i++ ))
    do
	    echo "============================="
	    echo "===$prog : $i"
	    echo "============================="
        $HIP $FLAG2 $prog
    done
done

echo "Running programs in $PARAHIP/parahip-benchmark/ ..."
for prog in $( ls $PARAHIP/parahip-benchmark/*.ss );
do
    sum=0
    for (( i = 1; i <= $ITERATIONS; i++ ))
    do
	    echo "============================="
	    echo "===$prog : $i"
	    echo "============================="
        $HIP $FLAG2 $prog
    done
done
