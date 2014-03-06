#!/bin/bash


# Run all tests, output to xls file for experimental comparison
# between parahip-rsr and parahip-org.
# parahip-rsr: parahip using threads as resource
# parahip-org: orignal parahip using threads as AND-conj

#HOME=.
HIP=../../../../hip

#EXAMPLE=~/hg/para5-threads/sleekex/examples/fracperm/threads

# Threads as resource
PARAHIP_RSR=~/hg/para5-threads/sleekex/examples/fracperm/threads/parahip-rsr
FLAG1="--en-para --en-thrd-resource -tp parahip --en-lsmu-infer"

# Threads as resource
EXAMPLE=~/hg/para5-threads/sleekex/examples/fracperm/threads

# Threads as AND-conjunction
PARAHIP_ORG=~/hg/para5-threads/sleekex/examples/fracperm/threads/parahip-org
FLAG2="--en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer"

ITERATIONS=10
LOG=run-all-logs_$(date +%b%d_%H%M)
#log all run
LOGRUN=$LOG-run.xls
#log the average
LOGAVG=$LOG-avg.xls
echo "Writing all runs to $LOGRUN ..."
echo "Writing average to $LOGAVG ..."

echo -e "Program\tIteration\tTime"  >> $LOGRUN

echo -e "Program\tLOC\tAvgTime"  >> $LOGAVG

echo "Running programs in $EXAMPLE ..."
for prog in $( ls $EXAMPLE/*.ss );
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


echo "Running programs in $PARAHIP_RSR ..."
for prog in $( ls $PARAHIP_RSR/*.ss );
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

echo "Running programs in $PARAHIP_ORG ..."
for prog in $( ls $PARAHIP_ORG/*.ss );
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
