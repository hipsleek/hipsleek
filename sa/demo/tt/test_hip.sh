CMD="../../../hip "
function one 
{
	sll_out=`../../../hip ../$1 --en-testing --pred-en-dangling  $2`
	rels=`echo "$sll_out" | awk '/rstart/,/rstop/'`
	defs=`echo "$sll_out" | awk '/dstart/,/dstop/'`
	echo "========$1 $2=========="
	echo "$rels"
	echo "$defs"
	echo "===================="
}
function two 
{
   one $1 $2 >& tests/hip/$1.out
}
two set-tail-2.ss "$1"
two sll-dll.ss "$1"
two last-2.ss  "$1"
two dll-append_paper.ss "--classic $1"
two zip_paper_leq.ss "--sa-en-sp-split $1"
two tll.ss "--sa-dnc $1"

