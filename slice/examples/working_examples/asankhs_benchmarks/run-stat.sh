TIMEOUT=600

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

for (( i = 10; i <= 20; i++ ))
do
	echo "[$1][.nslc] spaguetti-$i"
	echo "[$1][.nslc] spaguetti-$i" >> time.stat
	kill_proc
	(time ../../../../sleek --ufdp -tp $1 spaguetti-$i.slk --eps --dis-slicing --dis-imm --ep-stat $2) 1> spaguetti-$i.$1.nslc.stat 2>> time.stat

	echo "[$1][.slc] spaguetti-$i"
	echo "[$1][.slc] spaguetti-$i" >> time.stat
	kill_proc
	(time ../../../../sleek --ufdp -tp $1 spaguetti-$i.slk --eps --enable-slicing --dis-imm --ep-stat $2) 1> spaguetti-$i.$1.slc.stat 2>> time.stat

	echo "[$1][.ineq] spaguetti-$i"
	echo "[$1][.ineq] spaguetti-$i" >> time.stat
	kill_proc
	(time ../../../../sleek --ufdp -tp $1 spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm --ep-stat $2) 1> spaguetti-$i.$1.ineq.stat 2>> time.stat

done

kill_proc
