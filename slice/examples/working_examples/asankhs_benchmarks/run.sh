for (( i = 10; i <= 10; i++ ))
do
	echo "[z3] spaguetti-$i with eps"
	time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --dis-imm > spaguetti-$i.z3.eps
	echo "[z3] spaguetti-$i with slicing + eps"
	time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm > spaguetti-$i.z3.slc.eps

	echo "[spass] spaguetti-$i with eps"
	time ../../../../sleek --ufdp -tp spass spaguetti-$i.slk --eps --dis-imm > spaguetti-$i.spass.eps
	echo "[spass] spaguetti-$i with slicing + eps"
	time ../../../../sleek --ufdp -tp spass spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm > spaguetti-$i.spass.slc.eps
done
	
