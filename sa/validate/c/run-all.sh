#skip2-list, cll.c, check-cll: something wrong with conditional stmts
echo "ll-trav.ss"
../../../hip ll-trav.c -validate ../o/ll-trav.cp | grep Validate
echo "ll-trav-1.ss: ll with at least one node"
../../../hip ll-trav-1.c -validate ../o/ll-trav-1.cp | grep Validate
echo "sll-reverse"
../../hip sll-reverse.ss -validate o/sll-reverse.cp | grep Validate
echo "zip_paper_eq"
../../hip zip_paper_eq.c -validate ../o/zip_paper_eq.cp | grep Validate
echo "sll+head"
../../hip check-sll-head.ss -validate o/check-sll-head.cp | grep Validate
echo "check-sll-head"
../../hip check-sll-head.ss -validate o/check-sll-head.cp | grep Validate
echo "skip0"
../../hip skip0.ss -validate o/skip0.cp | grep Validate
echo "skip2-list: to fix the inference, rose-tree-1.ss"
../../hip skip2-list.ss -validate ../o/skip2-list.cp | grep Validate
echo "skip3-list"
#../../hip skip3-list.ss -validate o/skip3-list.cp | grep Validate
echo "check-sorted"
../../hip check-sorted.c --sa-en-pure-field -validate ../o/check-sorted.cp | grep Validate
echo "sll-insertsort: to check result of G"
#../../hip sll-insertsort.c -validate ../o/sll-insertsort.cp | grep Validate
echo "CSll: can not verify"
../../hip cll.c -validate ../o/cll.cp | grep Validate
echo "check-CSll: can not verify"
../../hip check-cll.c -validate ../o/check-cll.cp | grep Validate
echo " 0/1 SLLs"
../../hip sll-01-slls.c -validate o/sll-01-slls.cp | grep Validate
echo "sll2dll"
../../hip sll-dll.c -validate ../o/sll-dll.cp | grep Validate
echo "check-dll"
../../hip check-dll.ss -validate o/check-dll.cp | grep Validate
echo "bt-search-2.ss"
../../hip bt-search-2.c -validate  ../o/bt-search-2.cp | grep Validate
echo "tll"
../../hip tll.c --sa-dnc --pred-en-eup -validate ../o/tll.cp | grep Validate
echo "rose-tree to fix exception"
../../hip rose-tree-1.ss -validate o/rose-tree-1.cp | grep Validate
echo "check mcf: to fix exception (to fix bugs of validation)"
../../hip check-mcf.ss -validate o/check-mcf.cp | grep Validate
echo "check-tll: to check"
#../../hip check-tll.ss --sa-dnc --pred-en-dangling -validate o/check-tll.cp | grep Validate
echo "ll-back.ss"
#../../hip ll-back.ss
#sa-dangling
echo "dll-app"
../../hip dll-append_paper.c --classic --pred-en-dangling -validate ../o/dll-append_paper.cp | grep Validate
echo "tll"
../../hip tll.c --sa-dnc --pred-en-dangling --pred-en-eup -validate ../o/tll_dang.cp | grep Validate
#pred-disj-unify
echo "ll-trav-1.ss --pred-disj-unify"
../../hip ll-trav-1.c --pred-disj-unify -validate ../o/ll-trav-1-unify.cp | grep Validate

#pred-en-split
echo "cyc-lseg"
../../hip cyc-lseg.c  -validate ../o/cyc-lseg.cp --pred-en-split | grep Validate
echo "zip_paper_eq"
../../hip zip_paper_eq.c  -validate ../o/zip_paper_eq-split.cp --pred-en-split | grep Validate

#pred-unify-post
echo "cyc-tree (search)"
../../hip cyc-tree-1.c --pred-unify-post -validate ../o/cyc-tree-1.cp | grep Validate
echo "bt-search-2.ss"
../../hip bt-search-2.c -validate --pred-unify-post  ../o/bt-search-2.cp | grep Validate
#sa-dnc

#--pred-en-equiv
echo "cyc-lseg"
#../../hip ll-trav.c --pred-en-equiv -validate ../o/ll-trav-equiv.cp --pred-en-split | grep Validate