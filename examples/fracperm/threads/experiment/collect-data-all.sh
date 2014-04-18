#!/bin/bash


# Run all tests, output to xls file for experimental comparison
# between ThreadHIP and ParaHIP.

HIP=../../../../hip

# Threads as resource
THREADHIP=~/hg/para5-threads/sleekex/examples/fracperm/threads/threadhip
FLAG1="--en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic"



# Threads as AND-conjunction
PARAHIP=~/hg/para5-threads/sleekex/examples/fracperm/threads/parahip
FLAG2="--en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic"

ITERATIONS=1
LOG=run-all-logs_$(date +%b%d_%H%M)
#log all run
LOGRUN=$LOG-run.xls
#log the average
LOGAVG=$LOG-avg.xls
echo "Writing all runs to $LOGRUN ..."
echo "Writing average to $LOGAVG ..."

echo -e "Program\tIteration\tTime"  >> $LOGRUN

echo -e "Program\tLOC\tAvgTime"  >> $LOGAVG

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
        result=$($HIP $FLAG1 $prog | grep "Total verification" |  awk '{print $4}')
        echo -e "$prog\t$i\t$result" >> $LOGRUN
        sum=$(echo "$sum + $result" | bc -l)
    done
    avg=$(echo "$sum / $ITERATIONS" | bc -l)
    l=$(wc -l $prog |  awk '{print $1}')
    echo -e "$prog\t$l\t$avg" >> $LOGAVG
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
        result=$($HIP $FLAG1 $prog | grep "Total verification" |  awk '{print $4}')
        echo -e "$prog\t$i\t$result" >> $LOGRUN
        sum=$(echo "$sum + $result" | bc -l)
    done
    avg=$(echo "$sum / $ITERATIONS" | bc -l)
    l=$(wc -l $prog |  awk '{print $1}')
    echo -e "$prog\t$l\t$avg" >> $LOGAVG
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
        result=$($HIP $FLAG2 $prog | grep "Total verification" |  awk '{print $4}')
        echo -e "$prog\t$i\t$result" >> $LOGRUN
        sum=$(echo "$sum + $result" | bc -l)
    done
    avg=$(echo "$sum / $ITERATIONS" | bc -l)
    l=$(wc -l $prog |  awk '{print $1}')
    echo -e "$prog\t$l\t$avg" >> $LOGAVG
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
        result=$($HIP $FLAG2 $prog | grep "Total verification" |  awk '{print $4}')
        echo -e "$prog\t$i\t$result" >> $LOGRUN
        sum=$(echo "$sum + $result" | bc -l)
    done
    avg=$(echo "$sum / $ITERATIONS" | bc -l)
    l=$(wc -l $prog |  awk '{print $1}')
    echo -e "$prog\t$l\t$avg" >> $LOGAVG
done
