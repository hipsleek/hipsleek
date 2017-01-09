#Compare old result with new result
#================SLEEK==========================
#================SLEEK==========================
echo "======= thread-split.slk  ======"
diff test-cases/thread-split.slk.res test-cases/thread-split.slk.n
echo "======= thread-dead.slk  ======"
diff test-cases/thread-dead.slk.res test-cases/thread-dead.slk.n
echo "======= bag-of-pairs.slk ======"
diff test-cases/bag-of-pairs.slk.res test-cases/bag-of-pairs.slk.n
echo "======= wait2z.slk ======"
diff test-cases/wait2z.slk.res test-cases/wait2z.slk.n
echo "======= wait2.slk ======"
diff test-cases/wait2.slk.res test-cases/wait2.slk.n
echo "======= latch.slk  ======"
diff test-cases/latch.slk.res test-cases/latch.slk.n
echo "======= split-cnt.slk  ======"
diff test-cases/split-cnt.slk.res test-cases/split-cnt.slk.n
echo "======= latch4.slk  ======"
diff test-cases/latch4.slk.res test-cases/latch4.slk.n
echo "======= concrete.slk  ======"
diff test-cases/concrete.slk.res test-cases/concrete.slk.n
echo "======= concrete-bags.slk  ======"
diff test-cases/concrete-bags.slk.res test-cases/concrete-bags.slk.n

#================HIP==========================
#================HIP==========================
echo "======= thread-split.ss  ======"
diff test-cases/thread-split.ss.res test-cases/thread-split.ss.n
echo "======= thread-dead.ss  ======"
diff test-cases/thread-dead.ss.res test-cases/thread-dead.ss.n
echo "======= mapreduce.ss  ======"
diff test-cases/mapreduce.res test-cases/mapreduce.n
echo "======= latch.ss  ======"
diff test-cases/latch.ss.res test-cases/latch.ss.n
echo "======= latch2.ss  ======"
diff test-cases/latch2.ss.res test-cases/latch2.ss.n
echo "======= latch-exp1.ss  ======"
diff test-cases/latch-exp1.ss.res test-cases/latch-exp1.ss.n
echo "======= latch-exp2.ss  ======"
diff test-cases/latch-exp2.ss.res test-cases/latch-exp2.ss.n
echo "======= lock-exp.ss  ======"
diff test-cases/lock-exp.ss.res test-cases/lock-exp.ss.n
echo "======= lock-exp2.ss  ======"
diff test-cases/lock-exp2.ss.res test-cases/lock-exp2.ss.n
echo "======= lock-exp3.ss  ======"
diff test-cases/lock-exp3.ss.res test-cases/lock-exp3.ss.n
echo "======= lock-exp4.ss  ======"
diff test-cases/lock-exp4.ss.res test-cases/lock-exp4.ss.n

echo "======= fibonacci.ss  ======"
diff test-cases/fibonacci.ss.res test-cases/fibonacci.ss.n
echo "======= parallel-mergesort.ss  ======"
diff test-cases/parallel-mergesort.ss.res test-cases/parallel-mergesort.ss.n
echo "======= parallel-quicksort.ss  ======"
diff test-cases/parallel-quicksort.ss.res test-cases/parallel-quicksort.ss.n
echo "======= multi-join1.ss  ======"
diff test-cases/multi-join1.ss.res test-cases/multi-join1.ss.n
echo "======= multi-join2.ss  ======"
diff test-cases/multi-join2.ss.res test-cases/multi-join2.ss.n
echo "======= threadpool.ss  ======"
diff test-cases/threadpool.ss.res test-cases/threadpool.ss.n
echo "======= deadpool.ss  ======"
diff test-cases/deadpool.ss.res test-cases/deadpool.ss.n

