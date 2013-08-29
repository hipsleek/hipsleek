echo "ll-trav.ss"
../../hip ll-trav.ss -validate o/ll-trav.cp | grep Validate
echo "ll-trav-1.ss: ll with at least one node"
../../hip ll-trav-1.ss -validate o/ll-trav-1.cp | grep Validate

#pred-disj-unify
echo "ll-trav-1.ss --pred-disj-unify"
../../hip ll-trav-1.ss --pred-disj-unify -validate o/ll-trav-1-unify.cp | grep Validate

#pred-en-split