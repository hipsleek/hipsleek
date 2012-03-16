TIMEOUT=600
SLEEK_TIMEOUT=2.0

echo "**********************" >> time.stat
date >> time.stat
echo "**********************" >> time.stat

kill_proc () {
	killall -v oc
	killall -v z3
	killall -v reduce
	killall -v SPASS-MOD
	killall -v sleek
}

for (( i = 10; i <= 10; i++ ))
do
	echo "[$1][.nslc] spaguetti-$i"
	echo "[$1][.nslc] spaguetti-$i" >> time.stat
	kill_proc
	(time ../../../../sleek --ufdp -tp $1 spaguetti-$i.slk --eps --dis-slicing --ep-stat --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT $2) 1> spaguetti-$i.$1.nslc.stat 2>> time.stat

	echo "[$1][.slc] spaguetti-$i"
	echo "[$1][.slc] spaguetti-$i" >> time.stat
	kill_proc
	(time ../../../../sleek --ufdp -tp $1 spaguetti-$i.slk --eps --enable-slicing --ep-stat --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT $2) 1> spaguetti-$i.$1.slc.stat 2>> time.stat

	echo "[$1][.ineq] spaguetti-$i"
	echo "[$1][.ineq] spaguetti-$i" >> time.stat
	kill_proc
	(time ../../../../sleek --ufdp -tp $1 spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --ep-stat --dis-provers-timeout --sleek-timeout $SLEEK_TIMEOUT $2) 1> spaguetti-$i.$1.ineq.stat 2>> time.stat

done

kill_proc
