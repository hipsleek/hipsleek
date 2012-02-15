for (( i = 10; i <= 10; i++ ))
do
	echo "[spass][imm] spaguetti-$i"
	time ../../../../sleek --ufdp -tp spass spaguetti-$i.slk > spaguetti-$i.spass.imm
	
	echo "[spass][imm.slc] spaguetti-$i"
	time ../../../../sleek --ufdp -tp spass spaguetti-$i.slk --enable-slicing > spaguetti-$i.spass.imm.slc

	echo "[spass][imm.ineq] spaguetti-$i"
	time ../../../../sleek --ufdp -tp spass spaguetti-$i.slk --enable-slicing --slc-opt-ineq > spaguetti-$i.spass.imm.ineq

	echo "[spass][imm.eps] spaguetti-$i"
	time ../../../../sleek --ufdp -tp spass spaguetti-$i.slk --eps > spaguetti-$i.spass.imm.eps
	
	echo "[spass][imm.slc.eps] spaguetti-$i"
	time ../../../../sleek --ufdp -tp spass spaguetti-$i.slk --enable-slicing --eps > spaguetti-$i.spass.imm.slc.eps

	echo "[spass][imm.ineq.eps] spaguetti-$i"
	time ../../../../sleek --ufdp -tp spass spaguetti-$i.slk --enable-slicing --slc-opt-ineq --eps > spaguetti-$i.spass.imm.ineq.eps
done

