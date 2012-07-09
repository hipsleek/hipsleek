TIMEOUT=600

echo "**********************" >> time.z3.out
date >> time.z3.out
echo "**********************" >> time.z3.out

kill_proc () {
	killall -v z3
	killall -v oc
	killall -v sleek
}

for (( i = 10; i <= 20; i++ ))
do
	# Z3
	echo "[z3][.eps] spaguetti-$i"
	echo "[z3][.eps] spaguetti-$i" >> time.z3.out
	kill_proc
	(time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --dis-slicing -nofilter --dis-imm) 1> spaguetti-$i.z3.eps 2>> time.z3.out

	# echo "[z3-simplify][.eps] spaguetti-$i"
	# echo "[z3-simplify][.eps] spaguetti-$i" >> time.z3.out
	# kill_proc
	# (time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --dis-slicing -nofilter --dis-imm --z3-simplify) 1> spaguetti-$i.z3.eps 2>> time.z3.out

	echo "[z3][.slc.eps] spaguetti-$i"
	echo "[z3][.slc.eps] spaguetti-$i" >> time.z3.out
	kill_proc
	(time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --dis-imm) 1> spaguetti-$i.z3.slc.eps 2>> time.z3.out

	echo "[z3][.ineq.eps] spaguetti-$i"
	echo "[z3][.ineq.eps] spaguetti-$i" >> time.z3.out
	kill_proc
	(time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm) 1> spaguetti-$i.z3.ineq.eps 2>> time.z3.out
done

kill_proc
