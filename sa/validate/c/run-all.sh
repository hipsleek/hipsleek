HIP=../../../hip
echo "ll-trav.ss"
$HIP ll-trav.c -validate ../o/ll-trav.cp | grep Validate
echo "ll-trav-1.ss: ll with at least one node"
$HIP ll-trav-1.c -validate ../o/ll-trav-1.cp | grep Validate
echo "sll-reverse"
$HIP sll-reverse.c -validate ../o/sll-reverse.cp | grep Validate
echo "zip_paper_eq"
$HIP zip_paper_eq.c -validate ../o/zip_paper_eq.cp | grep Validate
echo "sll+head"
$HIP check-sll-head.c -validate ../o/check-sll-head.cp | grep Validate
echo "check-sll-head"
$HIP check-sll-head.c -validate ../o/check-sll-head.cp | grep Validate
echo "skip2-list"
$HIP skip2-list.c -validate ../o/skip2-list.cp | grep Validate
echo "skip3-list"
#$HIP skip3-list.c -validate ../o/skip3-list.cp | grep Validate
echo "check-sorted recursion"
$HIP check-sorted.c --sa-en-pure-field -validate ../o/check-sorted.cp | grep Validate
echo "check-sorted with while"
$HIP check-sorted-while.c --sa-en-pure-field -validate ../o/check-sorted.cp | grep Validate
echo "sll-insertsort: to check result of G"
#$HIP sll-insertsort.c -validate ../o/sll-insertsort.cp | grep Validate
echo "CSll"
$HIP cll.c -validate ../o/cll.cp | grep Validate
echo "check-CSll: can not verify"
$HIP check-cll.c -validate ../o/check-cll.cp | grep Validate
echo " 0/1 SLLs"
$HIP sll-01-slls.c -validate o/sll-01-slls.cp | grep Validate
echo "sll2dll"
$HIP sll-dll.c -validate ../o/sll-dll.cp | grep Validate
echo "check-dll"
$HIP check-dll.c -validate ../o/check-dll.cp | grep Validate
echo "bt-search-2."
$HIP bt-search-2.c -validate  ../o/bt-search-2.cp | grep Validate
echo "tll"
$HIP tll.c --sa-dnc --pred-en-eup -validate ../o/tll.cp | grep Validate
echo "rose-tree"
$HIP rose-tree-1.c -validate ../o/rose-tree-1.cp | grep Validate
echo "check mcf"
$HIP check-mcf.c -validate o/check-mcf.cp | grep Validate
echo "check-tll: to check"
#$HIP check-tll.ss --sa-dnc --pred-en-dangling -validate o/check-tll.cp | grep Validate
echo "ll-back.ss"
#$HIP ll-back.ss
#sa-dangling
echo "dll-app"
$HIP dll-append_paper.c --classic --pred-en-dangling -validate ../o/dll-append_paper.cp | grep Validate
echo "tll"
$HIP tll.c --sa-dnc --pred-en-dangling --pred-en-eup -validate ../o/tll_dang.cp | grep Validate
#pred-disj-unify
echo "ll-trav-1.ss --pred-disj-unify"
$HIP ll-trav-1.c --pred-disj-unify -validate ../o/ll-trav-1-unify.cp | grep Validate

#pred-en-split
echo "cyc-lseg"
$HIP cyc-lseg.c  -validate ../o/cyc-lseg.cp --pred-en-split | grep Validate
echo "zip_paper_eq"
$HIP zip_paper_eq.c  -validate ../o/zip_paper_eq-split.cp --pred-en-split | grep Validate

#pred-unify-post
echo "cyc-tree (search)"
$HIP cyc-tree-1.c --pred-unify-post -validate ../o/cyc-tree-1.cp | grep Validate
echo "bt-search-2.ss"
$HIP bt-search-2.c -validate --pred-unify-post  ../o/bt-search-2.cp | grep Validate
#sa-dnc

#--pred-en-equiv
echo "cyc-lseg"
#$HIP ll-trav.c --pred-en-equiv -validate ../o/ll-trav-equiv.cp --pred-en-split | grep Validate