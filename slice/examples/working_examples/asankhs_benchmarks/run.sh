for (( i = 10; i <= 20; i++ ))
do
	echo "spaguetti-$i with eps"
	time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --dis-imm > spaguetti-$i.res.eps
	echo "spaguetti-$i with slicing + eps"
	time ../../../../sleek --ufdp -tp z3 spaguetti-$i.slk --eps --enable-slicing --slc-opt-ineq --dis-imm > spaguetti-$i.res.slc.eps
done
	
