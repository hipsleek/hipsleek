for (( i = 10; i <= 20; i++ ))
do
	echo "[z3][.eps] spaguetti-$i"
	time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --dis-imm > spaguetti-$i.z3.eps
	echo "[z3][.ineq.eps] spaguetti-$i"
	time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm > spaguetti-$i.z3.ineq.eps
	echo "[z3][.slc.eps] spaguetti-$i"
	time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --dis-imm > spaguetti-$i.z3.slc.eps
done
	
