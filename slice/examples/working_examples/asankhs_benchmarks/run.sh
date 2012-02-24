echo "**********************" >> time.out
date >> time.out
echo "**********************" >> time.out

for (( i = 10; i <= 20; i++ ))
do
	# echo "[z3][.imm.eps] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps > spaguetti-$i.z3.imm.eps
	# echo "[z3][.imm.ineq.eps] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq > spaguetti-$i.z3.imm.ineq.eps
	# echo "[z3][.imm.slc.eps] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing > spaguetti-$i.z3.imm.slc.eps


	echo "[z3][.eps] spaguetti-$i"
	echo "[z3][.eps] spaguetti-$i" >> time.out
	(time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --dis-slicing --dis-imm) 1> spaguetti-$i.z3.eps 2>> time.out

	echo "[z3][.ineq.eps] spaguetti-$i"
	echo "[z3][.ineq.eps] spaguetti-$i" >> time.out
	(time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm) 1> spaguetti-$i.z3.ineq.eps 2>> time.out

	echo "[z3][.slc.eps] spaguetti-$i"
	echo "[z3][.slc.eps] spaguetti-$i" >> time.out
	(time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --dis-imm) 1> spaguetti-$i.z3.slc.eps 2>> time.out
	
	# echo "[oc][.eps] spaguetti-$i"
	# time ../../../../sleek --ufdp spaguetti-$i.slk --eps --dis-imm > spaguetti-$i.oc.eps
	echo "[oc][.ineq.eps] spaguetti-$i"
	echo "[oc][.ineq.eps] spaguetti-$i" >> time.out
	(time ../../../../sleek --ufdp spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm) 1> spaguetti-$i.oc.ineq.eps 2>> time.out
	# echo "[oc][.slc.eps] spaguetti-$i"
	# time ../../../../sleek --ufdp spaguetti-$i.slk --eps --enable-slicing --dis-imm > spaguetti-$i.oc.slc.eps

	# echo "[z3][] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --dis-imm > spaguetti-$i.z3
	# echo "[z3][.ineq] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --enable-slicing --slc-opt-ineq --dis-imm > spaguetti-$i.z3.ineq
	# echo "[z3][.slc] spaguetti-$i"
	# time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --enable-slicing --dis-imm > spaguetti-$i.z3.slc

done
	
