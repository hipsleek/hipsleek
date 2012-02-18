for (( i = 10; i <= 20; i++ ))
do
	grep Fail spaguetti-$i.z3.eps | sed 's/Entail (\([0-9]*\)).*/\1/' > z3.eps
	grep Fail spaguetti-$i.z3.slc.eps | sed 's/Entail (\([0-9]*\)).*/\1/' > z3.slc.eps
	grep Fail spaguetti-$i.z3.ineq.eps | sed 's/Entail (\([0-9]*\)).*/\1/' > z3.ineq.eps

	echo "[z3] (eps vs. slc.eps) spaguetti-$i"
	diff z3.eps z3.slc.eps

	echo "[z3] (eps vs. ineq.eps) spaguetti-$i"
	diff z3.eps z3.ineq.eps
done


