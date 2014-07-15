#create a list of expected results
#================SLEEK==========================
#================SLEEK==========================
echo "======= thread-split.slk ======"
../../sleek thread-split.slk | grep Entail > test-cases/thread-split.slk.res
echo "======= thread-dead.slk ======"
../../sleek thread-dead.slk | grep Entail > test-cases/thread-dead.slk.res
#================HIP==========================
#================HIP==========================
echo "======= thread-split.ss  ======"
../../hip thread-split.ss | grep -E 'Proc|assert:' > test-cases/thread-split.ss.res
echo "======= thread-dead.ss  ======"
../../hip thread-dead.ss | grep -E 'Proc|assert:' > test-cases/thread-dead.ss.res
echo "======= mapreduce.ss  ======"
../../hip mapreduce.ss | grep -E 'Proc|assert:' > test-cases/mapreduce.res