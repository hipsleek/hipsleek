function one 
{
	sll_out=`../../sleek --dis-time-stat --dis-count-stat ../$1 --en-testing  $2`
	#rels=`echo "$sll_out" | awk '/rstart/,/rstop/'`
	#defs=`echo "$sll_out" | awk '/dstart/,/dstop/'`
	echo "========$1 $2=========="
	#echo "$rels"
	#echo "$defs"
        echo "$sll_out"
	echo "===================="
}
function two 
{
   one $1 $2 >& tests/slk/$1.out
}
mkdir -p tests/slk
two lab1.slk --dump-proof
two lab2.slk --dump-proof
two lab3.slk --dump-proof
two lab4.slk --dump-proof
two test-3a.slk --dump-proof
two test-3b.slk --dump-proof
two test-3c.slk --dump-proof
two test-3d.slk --dump-proof
two test-3e.slk --dump-proof
two test-3f.slk --dump-proof
two test-3g.slk --dump-proof
two test-3h.slk --dump-proof
two test-3i.slk --dump-proof
