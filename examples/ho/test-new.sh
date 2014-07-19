# create a list of new results
# ================SLEEK==========================
# ================SLEEK==========================
echo "======= thread-split.slk ======"
../../sleek thread-split.slk -tp parahip | grep Entail > test-cases/thread-split.slk.n
echo "======= thread-dead.slk ======"
../../sleek thread-dead.slk -tp parahip | grep Entail > test-cases/thread-dead.slk.n
echo "======= bag-of-pairs.slk ======"
../../sleek bag-of-pairs.slk -tp parahip | grep Entail > test-cases/bag-of-pairs.slk.n
echo "======= wait2z.slk ======"
../../sleek wait2z.slk -tp parahip | grep "Entail\|Validate" > test-cases/wait2z.slk.n
echo "======= latch.slk ======"
../../sleek latch.slk -tp parahip | grep Entail > test-cases/latch.slk.n

#================HIP==========================
#================HIP==========================
echo "======= thread-split.ss  ======"
../../hip thread-split.ss -tp parahip | grep -E 'Proc|assert:' > test-cases/thread-split.ss.n
echo "======= thread-dead.ss  ======"
../../hip thread-dead.ss -tp parahip | grep -E 'Proc|assert:' > test-cases/thread-dead.ss.n
echo "======= mapreduce.ss  ======"
../../hip mapreduce.ss -tp parahip | grep -E 'Proc|assert:' > test-cases/mapreduce.n
echo "======= latch.ss  ======"
../../hip latch.ss -tp parahip | grep -E 'Proc|assert:' > test-cases/latch.ss.n
echo "======= latch2.ss  ======"
../../hip latch2.ss -tp parahip | grep -E 'Proc|assert:' > test-cases/latch2.ss.n
