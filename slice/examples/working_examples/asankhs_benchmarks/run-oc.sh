TIMEOUT=600

echo "**********************" >> time.oc.out
date >> time.oc.out
echo "**********************" >> time.oc.out

for (( i = 10; i <= 20; i++ ))
do
	# Omega
	echo "[oc][.eps] spaguetti-$i"
	echo "[oc][.eps] spaguetti-$i" >> time.oc.out
	time (./timeout -TERM $TIMEOUT ../../../../sleek --ufdp spaguetti-$i.slk --eps --dis-slicing --dis-imm) 1> spaguetti-$i.oc.eps 2>> time.oc.out

	echo "[oc][.slc.eps] spaguetti-$i"
	echo "[oc][.slc.eps] spaguetti-$i" >> time.oc.out
	time (./timeout -TERM $TIMEOUT ../../../../sleek --ufdp spaguetti-$i.slk --eps --enable-slicing --dis-imm) 1> spaguetti-$i.oc.slc.eps 2>> time.oc.out

	echo "[oc][.ineq.eps] spaguetti-$i"
	echo "[oc][.ineq.eps] spaguetti-$i" >> time.oc.out
	(time ../../../../sleek --ufdp spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm) 1> spaguetti-$i.oc.ineq.eps 2>> time.oc.out

	killall -v z3	
	killall -v reduce
	killall -v oc
	killall -v sleek
done

