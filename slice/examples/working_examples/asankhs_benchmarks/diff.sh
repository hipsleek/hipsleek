for (( i = 10; i <= 20; i++ ))
do
	grep Fail spaguetti-$i.z3.eps | sed 's/Entail (\([0-9]*\)).*/\1/' > z3.eps
	grep Fail spaguetti-$i.z3.slc.eps | sed 's/Entail (\([0-9]*\)).*/\1/' > z3.slc.eps

	grep Fail spaguetti-$i.spass | sed 's/Entail (\([0-9]*\)).*/\1/' > spass
	grep Fail spaguetti-$i.spass.slc | sed 's/Entail (\([0-9]*\)).*/\1/' > spass.slc

	echo "[z3] spaguetti-$i"
	diff z3.eps z3.slc.eps

	echo "[spass] spaguetti-$i"
	diff spass.eps spass.slc.eps

	echo "[z3-spass] spaguetti-$i"
	diff z3.eps spass

	echo "[z3-spass][slc] spaguetti-$i"
	diff z3.slc.eps spass.slc
done


