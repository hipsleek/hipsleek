for (( i = 10; i <= 20; i++ ))
do
	echo "[z3][eps] spaguetti-$i"
	time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --dis-imm > spaguetti-$i.z3.eps
	echo "[z3][slc.eps] spaguetti-$i"
	time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm > spaguetti-$i.z3.slc.eps

	echo "[spass][imm] spaguetti-$i"
	time ../../../../sleek --ufdp -tp spass spaguetti-$i.slk > spaguetti-$i.spass.imm
	echo "[spass][imm.slc] spaguetti-$i"
	time ../../../../sleek --ufdp -tp spass spaguetti-$i.slk --enable-slicing --slc-opt-ineq > spaguetti-$i.spass.imm.slc
done

