#!/bin/bash


# Run all tests and display output

THREADHIP=../../../../threadhip
PARAHIP=../../../../parahip

# Threads as resource
THREADHIP_DIR=../threadhip/
#FLAG1="--en-para --en-thrd-resource -tp parahip --en-lsmu-infer"
FLAG1="" #no need for flags if running in website, bundle, or vm

# Threads as AND-conjunction
PARAHIP_DIR=../parahip/
#FLAG2="--en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer"
FLAG2="" #no need for flags if running in website, bundle, or vm

ITERATIONS=1 # ALWAYS 1

#########################################
#########################################
echo "Running programs in $THREADHIP_DIR ..."
for prog in $( ls $THREADHIP_DIR/*.ss );
do
    sum=0
    for (( i = 1; i <= $ITERATIONS; i++ ))
    do
	    echo "============================="
	    echo "===$prog : $i"
	    echo "============================="
        $THREADHIP $FLAG1 $prog
    done
done

echo "Running programs in $THREADHIP_DIR/parahip-benchmark/ ..."
for prog in $( ls $THREADHIP_DIR/parahip-benchmark/*.ss );
do
    sum=0
    for (( i = 1; i <= $ITERATIONS; i++ ))
    do
	    echo "============================="
	    echo "===$prog : $i"
	    echo "============================="
        $THREADHIP $FLAG1 $prog
    done
done

#########################################
#########################################

echo "Running programs in $PARAHIP_DIR ..."
for prog in $( ls $PARAHIP_DIR/*.ss );
do
    sum=0
    for (( i = 1; i <= $ITERATIONS; i++ ))
    do
	    echo "============================="
	    echo "===$prog : $i"
	    echo "============================="
        $PARAHIP $FLAG2 $prog
    done
done

echo "Running programs in $PARAHIP_DIR/parahip-benchmark/ ..."
for prog in $( ls $PARAHIP_DIR/parahip-benchmark/*.ss );
do
    sum=0
    for (( i = 1; i <= $ITERATIONS; i++ ))
    do
	    echo "============================="
	    echo "===$prog : $i"
	    echo "============================="
        $PARAHIP $FLAG2 $prog
    done
done
