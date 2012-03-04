TIMEOUT=600

echo "**********************" >> time.rl.out
date >> time.rl.out
echo "**********************" >> time.rl.out

for (( i = 10; i <= 20; i++ ))
do
	# Redlog
	echo "[rl][.eps] spaguetti-$i"
	echo "[rl][.eps] spaguetti-$i" >> time.rl.out
	time (./timeout -TERM $TIMEOUT ../../../../sleek --ufdp -tp redlog --dis-oc spaguetti-$i.slk --eps --dis-slicing --dis-imm) 1> spaguetti-$i.rl.eps 2>> time.rl.out

	echo "[rl][.slc.eps] spaguetti-$i"
	echo "[rl][.slc.eps] spaguetti-$i" >> time.rl.out
	time (./timeout -TERM $TIMEOUT ../../../../sleek --ufdp -tp redlog --dis-oc spaguetti-$i.slk --eps --enable-slicing --dis-imm) 1> spaguetti-$i.rl.slc.eps 2>> time.rl.out

	echo "[rl][.ineq.eps] spaguetti-$i"
	echo "[rl][.ineq.eps] spaguetti-$i" >> time.rl.out
	(time ../../../../sleek --ufdp -tp redlog --dis-oc spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm) 1> spaguetti-$i.rl.ineq.eps 2>> time.rl.out

	killall -v z3
	killall -v reduce
	killall -v oc
	killall -v sleek
done

