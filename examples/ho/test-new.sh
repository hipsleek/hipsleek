# create a list of new results
# ================SLEEK==========================
# ================SLEEK==========================
echo "======= thread-split.slk ======"
../../sleek thread-split.slk | grep Entail > test-cases/thread-split.slk.n
echo "======= thread-dead.slk ======"
../../sleek thread-dead.slk | grep Entail > test-cases/thread-dead.slk.n

#================HIP==========================
#================HIP==========================
echo "======= thread-split.ss  ======"
../../hip thread-split.ss | grep -E 'Proc|assert:' > test-cases/thread-split.ss.n
echo "======= thread-dead.ss  ======"
../../hip thread-dead.ss | grep -E 'Proc|assert:' > test-cases/thread-dead.ss.n
echo "======= mapreduce.ss  ======"
../../hip mapreduce.ss | grep -E 'Proc|assert:' > test-cases/mapreduce.n