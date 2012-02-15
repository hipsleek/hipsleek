for (( i = 10; i <= 20; i++ ))
do
	grep Fail spaguetti-$i.res.eps | sed 's/Entail (\([0-9]*\)).*/\1/' > f.eps
	grep Fail spaguetti-$i.res.slc.eps | sed 's/Entail (\([0-9]*\)).*/\1/' > f.slc.eps
	echo "spaguetti-$i"
	diff f.eps f.slc.eps
done


