EX="./test_ex.sh ../hip"
mkdir -p ref/bugs/
mkdir -p result/bugs/
mkdir -p ref/field/
mkdir -p result/field/
mkdir -p ref/hip/
mkdir -p result/hip/
mkdir -p ref/inf/
mkdir -p result/inf/
mkdir -p ref/inf-imm/
mkdir -p result/inf-imm/
mkdir -p ref/norm/
mkdir -p result/norm/
mkdir -p ref/slk/
mkdir -p result/slk/
$EX bugs/clist1.ss
$EX bugs/clist2a.ss
$EX bugs/clist2.ss
$EX bugs/clist.ss
$EX hip/getset.ss
$EX hip/imspd.ss
$EX hip/insertion_simple.ss
$EX hip/insertion.ss
$EX hip/length.ss
$EX hip/qsort.ss
$EX hip/reverse.ss
$EX hip/schorr-waite-list.ss
$EX hip/sll.ss
$EX hip/test1.ss
$EX hip/test2.ss
$EX hip/test3.ss
$EX inf/cell-1.ss
$EX inf/cell-2.ss
$EX inf/cell-3b.ss
$EX inf/cell-3c.ss
$EX inf/cell-3.ss
$EX inf/lend-3a.ss
