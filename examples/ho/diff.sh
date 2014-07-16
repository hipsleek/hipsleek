#Compare old result with new result
#================SLEEK==========================
#================SLEEK==========================
echo "======= thread-split.ss  ======"
diff test-cases/thread-split.slk.res test-cases/thread-split.slk.n
echo "======= thread-dead.ss  ======"
diff test-cases/thread-dead.slk.res test-cases/thread-dead.slk.n
echo "======= latch.slk  ======"
diff test-cases/latch.slk.res test-cases/latch.slk.n

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
