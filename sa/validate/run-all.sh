echo "ll-trav.ss"
../../hip ll-trav.ss -validate o/ll-trav.cp | grep Validate
echo "ll-trav-1.ss: ll with at least one node"
../../hip ll-trav-1.ss -validate o/ll-trav-1.cp | grep Validate
echo "sll-reverse"
../../hip sll-reverse.ss  -validate o/sll-reverse.cp | grep Validate
echo "zip_paper_eq"
../../hip zip_paper_eq.ss  -validate o/zip_paper_eq.cp | grep Validate
echo "sll+head"
../../hip check-sll-head.ss -validate o/check-sll-head.cp | grep Validate
echo "check-dll"
../../hip check-dll.ss  -validate o/check-dll.cp | grep Validate
echo "check-sll-head"
../../hip check-sll-head.ss  -validate o/check-sll-head.cp | grep Validate
echo "skip0"
../../hip skip0.ss  -validate o/skip0.cp | grep Validate
#echo "skip-list"
#../../hip skip-list.ss  -validate o/skip-list.cp | grep Validate
echo "check-sorted"
../../hip check-sorted.ss  --sa-en-pure-field  -validate o/check-sorted.cp | grep Validate
#echo "sll-insertsort.ss"
#../../hip sll-insertsort.ss -validate o/sll-insertsort.cp | grep Validate
echo "CSll"
../../hip cll.ss  -validate o/cll.cp | grep Validate
echo "check-CSll"
../../hip check-cll.ss  -validate o/check-cll.cp | grep Validate
echo " 0/1 SLLs"
../../hip sll-01-slls.ss  -validate o/sll-01-slls.cp | grep Validate
#sa-dangling

#pred-disj-unify
echo "ll-trav-1.ss --pred-disj-unify"
../../hip ll-trav-1.ss --pred-disj-unify -validate o/ll-trav-1-unify.cp | grep Validate

#pred-en-split
echo "cyc-lseg"
../../hip cyc-lseg.ss  -validate o/cyc-lseg.cp --pred-en-split | grep Validate
echo "zip_paper_eq"
../../hip zip_paper_eq.ss  -validate o/zip_paper_eq-split.cp --pred-en-split | grep Validate