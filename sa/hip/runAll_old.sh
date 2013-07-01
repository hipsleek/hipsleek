echo "ll-append3.ss"
../../hip ll-append3.ss --sa-dangling -cp-test cp/ll-append3.cp | grep Compare
echo "ll-append4.ss"
../../hip ll-append4.ss --sa-dangling  --sa-inlining -cp-test cp/ll-append4.cp | grep Compare
echo "ll-append5.ss wo dangling"
../../hip ll-append5.ss  --sa-useless -cp-test cp/ll-append5_elim.cp | grep Compare
echo "ll-append5.ss with danling"
../../hip ll-append5.ss --sa-dangling --sa-inlining --sa-useless -cp-test cp/ll-append5.cp | grep Compare
echo "ll-append6.ss"
../../hip ll-append6.ss --sa-dangling -cp-test cp/ll-append6.cp | grep Compare
echo "ll-append7.ss"
../../hip ll-append7.ss --sa-dangling -cp-test cp/ll-append7.cp | grep Compare
echo "app.ss"
../../hip app.ss  -cp-test cp/app.cp | grep Compare
echo "ll-append8.ss with --sa-danling "
../../hip ll-append8.ss --sa-dangling -cp-test cp/ll-append8_w_dl.cp | grep Compare
echo "ll-append8.ss with --sa-danling "
../../hip ll-append8.ss --sa-dangling -cp-test cp/ll-append8_w_dl.cp | grep Compare
echo "ll-append8.ss with --sa-danling --sa-inlining"
../../hip ll-append8.ss --sa-dangling --sa-inlining -cp-test cp/ll-append8_dl_inl.cp | grep Compare
echo "ll-append9.ss"
../../hip ll-append9.ss --sa-dangling --sa-inlining -cp-test cp/ll-append9.cp | grep Compare
echo "ll-append10.ss"
../../hip ll-append10.ss --sa-dangling --sa-inlining -cp-test cp/ll-append10.cp | grep Compare
echo "ll-append15.ss"
../../hip ll-append15.ss --sa-dangling --sa-inlining -cp-test cp/ll-append15.cp | grep Compare
echo "qsort-2.ss"
../../hip qsort-2.ss --sa-dangling --sa-inlining -cp-test cp/qsort-2.cp | grep Compare
echo "dangling/ll-app3.ss"
../../hip dangling/ll-app3.ss --sa-dangling --sa-inlining -cp-test cp/ll-app3.cp | grep Compare
echo "dangling/ll-app4.ss"
../../hip dangling/ll-app4.ss --sa-dangling --sa-inlining -cp-test cp/ll-app4.cp | grep Compare
echo "dangling/ll-app5b.ss"
../../hip dangling/ll-app5b.ss --sa-useless -cp-test cp/ll-app5b.cp | grep Compare
echo "dangling/ll-app6.ss"
../../hip dangling/ll-app6.ss --sa-dangling --sa-inlining -cp-test cp/ll-app6.cp | grep Compare
echo "dangling/ll-swap.ss"
../../hip dangling/ll-swap.ss --sa-dangling --sa-inlining -cp-test cp/ll-swap.cp | grep Compare
echo "ex1.ss"
../../hip ex1.ss --sa-dangling -cp-test cp/ex1.cp | grep Compare
echo "ex1a.ss"
../../hip ex1a.ss --sa-dangling -cp-test cp/ex1a.cp | grep Compare
echo "ll-get-next"
../../hip ll-get-next.ss --sa-dangling --sa-inlining -cp-test cp/ll-get-next.cp | grep Compare
echo "dangling/get-next"
../../hip dangling/get-next.ss --sa-dangling --sa-inlining -cp-test cp/get-next.cp | grep Compare
echo "dangling/get-next2"
../../hip dangling/get-next2.ss --sa-dangling --sa-inlining -cp-test cp/get-next2.cp | grep Compare
echo "dangling/get-next3"
../../hip dangling/get-next3.ss --sa-dangling --sa-inlining -cp-test cp/get-next3.cp | grep Compare
echo "dangling/get-next4"
../../hip dangling/get-next4.ss --sa-dangling --sa-inlining -cp-test cp/get-next4.cp | grep Compare
echo "ll-get-next-next"
../../hip ll-get-next-next.ss --sa-dangling --sa-inlining -cp-test cp/ll-get-next-next.cp | grep Compare
echo "ll-next2"
../../hip ll-next2.ss --sa-dangling --sa-inlining -cp-test cp/ll-next2.cp | grep Compare
echo "ll-next3"
../../hip ll-next3.ss -cp-test cp/ll-next3.cp | grep Compare
echo "ll-next4"
../../hip ll-next4.ss --sa-dangling --sa-inlining -cp-test cp/ll-next4.cp | grep Compare
echo "ll-next5"
../../hip ll-next5.ss --sa-dangling --sa-inlining -cp-test cp/ll-next5.cp | grep Compare
echo "ll-next6"
../../hip ll-next6.ss --sa-dangling --sa-split --sa-inlining --sa-inlining -cp-test cp/ll-next6.cp | grep Compare
echo "ll-delete"
../../hip ll-delete.ss --sa-dangling --sa-inlining --sa-useless -cp-test cp/ll-delete.cp | grep Compare
# echo "ll-delete2"
# ../../hip ll-delete2.ss --sa-dangling --sa-inlining -cp-test cp/ll-delete2.cp | grep Compare
echo "ll-get_size"
../../hip ll-get-size.ss --sa-dangling -cp-test cp/ll-get-size.cp | grep Compare
echo "ll_all1"
../../hip ll_all1.ss --sa-dangling --sa-inlining -cp-test cp/ll_all1.cp | grep Compare
echo "ll_all3"
../../hip ll_all3.ss --sa-dangling -cp-test cp/ll_all3.cp | grep Compare
echo "ll_all4"
../../hip ll_all4.ss --sa-dangling --sa-inlining -cp-test cp/ll_all4.cp | grep Compare
echo "ll_all5"
../../hip ll_all5.ss --sa-dangling --sa-inlining --sa-split -cp-test cp/ll_all5.cp | grep Compare
echo "ll_all7"
../../hip ll_all7.ss --sa-dangling --sa-inlining -cp-test cp/ll_all7.cp | grep Compare
echo "ll_all8"
../../hip ll_all8.ss --sa-dangling --sa-inlining -cp-test cp/ll_all8.cp | grep Compare
echo "ll_all10"
../../hip ll_all10.ss --sa-dangling --sa-inlining -cp-test cp/ll_all10.cp | grep Compare
echo "ll_all_13"
../../hip ll_all_13.ss -cp-test cp/ll_all_13.cp | grep Compare
echo "ll_all_13a"
../../hip ll_all_13a.ss -cp-test cp/ll_all_13a.cp | grep Compare
echo "ll_all_13b"
../../hip ll_all_13b.ss -cp-test cp/ll_all_13b.cp | grep Compare
echo "ll_all_13c"
../../hip ll_all_13c.ss -cp-test cp/ll_all_13c.cp | grep Compare
echo "ll_all_13c1"
../../hip ll_all_13c1.ss -cp-test cp/ll_all_13c1.cp | grep Compare
echo "ll_all_13e"
../../hip ll_all_13e.ss -cp-test cp/ll_all_13e.cp | grep Compare
echo "ll_all_14"
../../hip ll_all_14.ss -cp-test cp/ll_all_14.cp | grep Compare
echo "mul-procs "
../../hip mul-procs.ss -cp-test cp/mul-procs.cp | grep Compare
echo "fun-call"
../../hip fun-call.ss -cp-test cp/fun_call.cp | grep Compare
echo "ll-empty"
../../hip ll-empty.ss -cp-test cp/ll-empty.cp | grep Compare
echo "ll-size"
../../hip ll-size.ss -cp-test cp/ll-size.cp | grep Compare
echo "ll-insert"
../../hip ll-insert.ss -cp-test cp/ll-insert.cp | grep Compare
echo "sll-del"
../../hip sll-del.ss -cp-test cp/sll-del.cp | grep Compare
echo "sll-del2"
../../hip sll-del2.ss -cp-test cp/sll-del2.cp | grep Compare
echo "ll-create"
../../hip ll-create.ss -cp-test cp/ll-create.cp | grep Compare
echo "dll-del0"
../../hip dll-del0.ss --sa-dangling --sa-inlining -cp-test cp/dll-del0.cp | grep Compare
echo "dll-del3"
../../hip dll-del3.ss --sa-dangling --sa-inlining --sa-refine-dang -cp-test cp/dll-del3.cp | grep Compare
echo "dll-del3a"
../../hip dll-del3a.ss --sa-dangling --sa-inlining --sa-refine-dang -cp-test cp/dll-del3a.cp | grep Compare
echo "ll-size1"
../../hip ll-size1.ss -cp-test cp/ll-size1.cp | grep Compare
echo "ll-ret-first"
../../hip ll-ret-first.ss --sa-dangling --sa-inlining -cp-test cp/ll-ret-first.cp | grep Compare
echo "ll-ret-first1"
../../hip ll-ret-first1.ss --sa-dangling --sa-inlining -cp-test cp/ll-ret-first1.cp | grep Compare
echo "bt-count-1.ss"
../../hip bt-count-1.ss -cp-test cp/bt-count-1.cp | grep Compare
echo "bt-trav.ss"
../../hip bt-trav.ss  -cp-test cp/bt-trav.cp | grep Compare
echo "bt-left2.ss"
../../hip bt-left2.ss  --sa-tree-simp -cp-test cp/bt-left2.cp | grep Compare
echo "bt-search-2.ss"
../../hip bt-search-2.ss --sa-tree-simp -cp-test cp/bt-search-2.cp | grep Compare
echo "ll-ret-first2: have not captured non-ptr values"
../../hip ll-ret-first2.ss --sa-dangling --sa-inlining -cp-test cp/ll-ret-first2.cp | grep Compare
