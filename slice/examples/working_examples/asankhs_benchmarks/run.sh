for (( i = 10; i <= 10; i++ ))
do
	# echo "[z3][.imm.eps] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps > spaguetti-$i.z3.imm.eps
	# echo "[z3][.imm.ineq.eps] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq > spaguetti-$i.z3.imm.ineq.eps
	# echo "[z3][.imm.slc.eps] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing > spaguetti-$i.z3.imm.slc.eps


	echo "[z3][.eps] spaguetti-$i"
	time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --dis-imm > spaguetti-$i.z3.eps
	echo "[z3][.ineq.eps] spaguetti-$i"
	time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm > spaguetti-$i.z3.ineq.eps
	echo "[z3][.slc.eps] spaguetti-$i"
	time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --dis-imm > spaguetti-$i.z3.slc.eps
	
	# echo "[oc][.eps] spaguetti-$i"
	# time ../../../../sleek --ufdp spaguetti-$i.slk --eps --dis-imm > spaguetti-$i.oc.eps
	echo "[oc][.ineq.eps] spaguetti-$i"
	time ../../../../sleek --ufdp spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm > spaguetti-$i.oc.ineq.eps
	# echo "[oc][.slc.eps] spaguetti-$i"
	# time ../../../../sleek --ufdp spaguetti-$i.slk --eps --enable-slicing --dis-imm > spaguetti-$i.oc.slc.eps

	# echo "[z3][] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --dis-imm > spaguetti-$i.z3
	# echo "[z3][.ineq] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --enable-slicing --slc-opt-ineq --dis-imm > spaguetti-$i.z3.ineq
	# echo "[z3][.slc] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --enable-slicing --dis-imm > spaguetti-$i.z3.slc

done
	
