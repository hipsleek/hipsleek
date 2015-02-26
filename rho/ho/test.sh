#create a list of expected results
#================SLEEK==========================
#================SLEEK==========================
echo "======= thread-split.slk ======"
../../sleek thread-split.slk -tp parahip | grep Entail > test-cases/thread-split.slk.res
echo "======= thread-dead.slk ======"
../../sleek thread-dead.slk -tp parahip | grep Entail > test-cases/thread-dead.slk.res
echo "======= bag-of-pairs.slk ======"
../../sleek bag-of-pairs.slk -tp parahip | grep Entail > test-cases/bag-of-pairs.slk.res
echo "======= wait2z.slk ======"
../../sleek wait2z.slk -tp parahip | grep "Entail\|Validate" > test-cases/wait2z.slk.res
echo "======= wait2.slk ======"
../../sleek wait2.slk -tp parahip | grep "Entail\|Validate" > test-cases/wait2.slk.res
echo "======= latch.slk ======"
../../sleek latch.slk -tp parahip | grep Entail > test-cases/latch.slk.res
echo "======= split-cnt.slk ======"
../../sleek split-cnt.slk -tp parahip | grep "Entail\|Validate" > test-cases/split-cnt.slk.res
echo "======= latch4.slk ======"
../../sleek latch4.slk -tp parahip | grep "Entail\|Validate" > test-cases/latch4.slk.res
echo "======= concrete.slk ======"
../../sleek concrete.slk -tp parahip | grep "Entail\|Validate" > test-cases/concrete.slk.res
echo "======= concrete-bags.slk ======"
../../sleek concrete-bags.slk -tp parahip | grep "Entail\|Validate" > test-cases/concrete-bags.slk.res

#================HIP==========================
#================HIP==========================
echo "======= thread-split.ss  ======"
../../hip thread-split.ss -tp parahip --classic | grep -E 'Proc|assert:' > test-cases/thread-split.ss.res
echo "======= thread-dead.ss  ======"
../../hip thread-dead.ss -tp parahip | grep -E 'Proc|assert:' > test-cases/thread-dead.ss.res
echo "======= mapreduce.ss  ======"
../../hip mapreduce.ss -tp parahip --classic | grep -E 'Proc|assert:' > test-cases/mapreduce.res
echo "======= latch.ss  ======"
../../hip latch.ss -tp parahip --classic | grep -E 'Proc|assert:' > test-cases/latch.ss.res
echo "======= latch2.ss  ======"
../../hip latch2.ss -tp parahip --classic | grep -E 'Proc|assert:' > test-cases/latch2.ss.res
echo "======= latch-exp1.ss  ======"
../../hip latch-exp1.ss -tp parahip --classic | grep -E 'Proc|assert:' > test-cases/latch-exp1.ss.res
echo "======= latch-exp2.ss  ======"
../../hip latch-exp2.ss -tp parahip --classic | grep -E 'Proc|assert:|cause:' > test-cases/latch-exp2.ss.res
echo "======= lock-exp.ss  ======"
../../hip lock-exp.ss -tp parahip --classic | grep -E 'Proc|assert:' > test-cases/lock-exp.ss.res
echo "======= lock-exp2.ss  ======"
../../hip lock-exp2.ss -tp parahip --classic | grep -E 'Proc|assert:' > test-cases/lock-exp2.ss.res
echo "======= lock-exp3.ss (slow)  ======"
../../hip lock-exp3.ss -tp parahip -perm fperm --classic | grep -E 'Proc|assert:|cause:' > test-cases/lock-exp3.ss.res
echo "======= lock-exp4.ss (slow)  ======"
../../hip lock-exp4.ss -tp parahip -perm fperm --classic | grep -E 'Proc|assert:|cause:' > test-cases/lock-exp4.ss.res

echo "======= fibonacci.ss  ======"
../../hip fibonacci.ss -tp parahip --classic | grep -E 'Proc|assert:' > test-cases/fibonacci.ss.res
echo "======= parallel-mergesort.ss  ======"
../../hip parallel-mergesort.ss -tp parahip --classic | grep -E 'Proc|assert:' > test-cases/parallel-mergesort.ss.res
echo "======= parallel-quicksort.ss  ======"
../../hip parallel-quicksort.ss -tp parahip --classic | grep -E 'Proc|assert:' > test-cases/parallel-quicksort.ss.res
echo "======= multi-join1.ss  ======"
../../hip multi-join1.ss -tp parahip --classic | grep -E 'Proc|assert:' > test-cases/multi-join1.ss.res
echo "======= multi-join2.ss  ======"
../../hip multi-join2.ss -tp parahip -perm fperm --classic | grep -E 'Proc|assert:' > test-cases/multi-join2.ss.res
echo "======= threadpool.ss  ======"
../../hip threadpool.ss -tp parahip -perm fperm --classic | grep -E 'Proc|assert:' > test-cases/threadpool.ss.res
echo "======= deadpool.ss  ======"
../../hip deadpool.ss -tp parahip -perm fperm --classic | grep -E 'Proc|assert:' > test-cases/deadpool.ss.res