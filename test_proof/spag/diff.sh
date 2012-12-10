for (( i = 10; i <= 10; i++ ))
do
	grep Fail spaguetti-$i.z3.eps | sed 's/Entail (\([0-9]*\)).*/\1/' > z3.eps
	grep Fail spaguetti-$i.z3.slc.eps | sed 's/Entail (\([0-9]*\)).*/\1/' > z3.slc.eps
	grep Fail spaguetti-$i.z3.ineq.eps | sed 's/Entail (\([0-9]*\)).*/\1/' > z3.ineq.eps
	
	# grep Fail spaguetti-$i.z3 | sed 's/Entail (\([0-9]*\)).*/\1/' > z3
	# grep Fail spaguetti-$i.z3.slc | sed 's/Entail (\([0-9]*\)).*/\1/' > z3.slc
	# grep Fail spaguetti-$i.z3.ineq | sed 's/Entail (\([0-9]*\)).*/\1/' > z3.ineq
	
	grep Fail spaguetti-$i.oc.ineq.eps | sed 's/Entail (\([0-9]*\)).*/\1/' > oc.ineq.eps

	echo "[z3] (eps vs. slc.eps) spaguetti-$i"
	diff z3.eps z3.slc.eps

	echo "[z3] (eps vs. ineq.eps) spaguetti-$i"
	diff z3.eps z3.ineq.eps
	
	echo "[z3 vs. oc] (ineq.eps) spaguetti-$i"
	diff z3.ineq.eps oc.ineq.eps
	
	# echo "[z3] (eps vs. no_eps) spaguetti-$i"
	# diff z3.eps z3

	# echo "[z3] (slc.eps vs. slc) spaguetti-$i"
	# diff z3.slc.eps z3.slc
	
	# echo "[z3] (ineq.eps vs. ineq) spaguetti-$i"
	# diff z3.ineq.eps z3.ineq
done


