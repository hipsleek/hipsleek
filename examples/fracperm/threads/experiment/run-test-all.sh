#!/bin/bash


# Run all tests, ensure correct results before deloy
# Save all output into the log file LOG for furture check

#HOME=.
HIP=../../../../hip
EXAMPLE=~/hg/para5-threads2/sleekex/examples/fracperm/threads
PARAHIP=~/hg/para5-threads2/sleekex/examples/fracperm/threads/parahip
ITERATIONS=1
LOG=run-all-logs_$(date +%b%d_%H%M)
#log all run
LOGRUN=$LOG-run.xls
#log the average
LOGAVG=$LOG-avg.xls
echo "Writing all runs to $LOGRUN ..."
echo "Writing average to $LOGAVG ..."

echo "Running programs in $EXAMPLE ..."
for prog in $( ls $EXAMPLE/*.ss );
do
    sum=0
    for (( i = 1; i <= $ITERATIONS; i++ ))
    do
	    echo "============================="
	    echo "===$prog : $i"
	    echo "============================="
        result=$($HIP --en-para --en-thrd-resource -tp parahip --en-lsmu-infer $prog | grep "Total verification" |  awk '{print $4}')
        echo -e "$prog\t$i\t$result" >> $LOGRUN
        sum=$(echo "$sum + $result" | bc -l)
    done
    avg=$(echo "$sum / $ITERATIONS" | bc -l)
    echo -e "$prog\t$avg" >> $LOGAVG
done

echo "Running programs in $PARAHIP ..."
for prog in $( ls $PARAHIP/*.ss );
do
    sum=0
    for (( i = 1; i <= $ITERATIONS; i++ ))
    do
	    echo "============================="
	    echo "===$prog : $i"
	    echo "============================="
        result=$($HIP --en-para --en-thrd-resource -tp parahip --en-lsmu-infer $prog | grep "Total verification" |  awk '{print $4}')
        echo -e "$prog\t$i\t$result" >> $LOGRUN
        sum=$(echo "$sum + $result" | bc -l)
    done
    avg=$(echo "$sum / $ITERATIONS" | bc -l)
    echo -e "$prog\t$avg" >> $LOGAVG
done
