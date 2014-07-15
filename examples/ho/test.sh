#create a list of expected results
#================SLEEK==========================
#================SLEEK==========================
echo "======= thread-split.slk ======"
../../sleek thread-split.slk | grep Entail > test-cases/thread-split.slk.res
echo "======= thread-dead.slk ======"
../../sleek thread-dead.slk | grep Entail > test-cases/thread-dead.slk.res
echo "======= latch.slk ======"
../../sleek latch.slk | grep Entail > test-cases/latch.slk.res
#================HIP==========================
#================HIP==========================
echo "======= thread-split.ss  ======"
../../hip thread-split.ss | grep -E 'Proc|assert:' > test-cases/thread-split.ss.res
echo "======= thread-dead.ss  ======"
../../hip thread-dead.ss | grep -E 'Proc|assert:' > test-cases/thread-dead.ss.res
echo "======= mapreduce.ss  ======"
../../hip mapreduce.ss | grep -E 'Proc|assert:' > test-cases/mapreduce.res
echo "======= latch.ss  ======"
../../hip latch.ss | grep -E 'Proc|assert:' > test-cases/latch.ss.res
echo "======= latch2.ss  ======"
../../hip latch2.ss | grep -E 'Proc|assert:' > test-cases/latch2.ss.res
