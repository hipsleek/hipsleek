#Compare old result with new result
#================SLEEK==========================
#================SLEEK==========================
echo "======= thrd1.slk ======"
diff test-cases/thrd1.res test-cases/thrd1.n

#================HIP==========================
#================HIP==========================
echo "======= motiv-example.ss  ======"
diff test-cases/motiv-example.res test-cases/motiv-example.n
echo "======= motiv-example2.ss  ======"
diff test-cases/motiv-example2.res test-cases/motiv-example2.n
echo "======= no-deadlock-nonlexical.ss ======"
diff test-cases/no-deadlock-nonlexical.res test-cases/no-deadlock-nonlexical.n
echo "======= no-deadlock-nonlexical2.ss ======"
diff test-cases/no-deadlock-nonlexical2.res test-cases/no-deadlock-nonlexical2.n

#================PARAHIP==========================
#================PARAHIP==========================
# echo "======= parahip/simple.ss ======"
# ##No Fork/Join
# diff test-cases/parahip/simple.res test-cases/parahip/simple.n

echo "======= parahip/forkjoin.ss ======"
diff test-cases/parahip/forkjoin.res test-cases/parahip/forkjoin.n

# echo "======= parahip/cell.ss ======"
# ##No Fork/Join
# diff test-cases/parahip/cell.res test-cases/parahip/cell.n

echo "======= parahip/cell4.ss ======"
diff test-cases/parahip/cell4.res test-cases/parahip/cell4.n

# echo "======= parahip/cell-lock-vperm.ss ======"
# ##No Fork/Join
# diff test-cases/parahip/cell-lock-vperm.res test-cases/parahip/cell-lock-vperm.n

# echo "======= parahip/cell-extreme-cases.ss ======"
# ##No Fork/Join
# diff test-cases/parahip/cell-extreme-cases.res test-cases/parahip/cell-extreme-cases.n

echo "======= parahip/ls-bind.ss ======"
diff test-cases/parahip/ls-bind.res test-cases/parahip/ls-bind.n

# echo "======= parahip/ls-waitlevel2.ss ======"
# ##No Fork/Join
# diff test-cases/parahip/ls-waitlevel2.res test-cases/parahip/ls-waitlevel2.n

# echo "======= parahip/double-acquire.ss ======"
# ##No Fork/Join
# diff test-cases/parahip/double-acquire.res test-cases/parahip/double-acquire.n

echo "======= parahip/no-deadlock1.ss ======"
diff test-cases/parahip/no-deadlock1.res test-cases/parahip/no-deadlock1.n

echo "======= parahip/no-deadlock2.ss ======"
diff test-cases/parahip/no-deadlock2.res test-cases/parahip/no-deadlock2.n

echo "======= parahip/no-deadlock3.ss ======"
diff test-cases/parahip/no-deadlock3.res test-cases/parahip/no-deadlock3.n

echo "======= parahip/deadlock1.ss ======"
diff test-cases/parahip/deadlock1.res test-cases/parahip/deadlock1.n

echo "======= parahip/deadlock2.ss ======"
diff test-cases/parahip/deadlock2.res test-cases/parahip/deadlock2.n

echo "======= parahip/deadlock3.ss ======"
diff test-cases/parahip/deadlock3.res test-cases/parahip/deadlock3.n

echo "======= parahip/disj-no-deadlock1.ss ======"
diff test-cases/parahip/disj-no-deadlock1.res test-cases/parahip/disj-no-deadlock1.n

echo "======= parahip/disj-no-deadlock2.ss ======"
diff test-cases/parahip/disj-no-deadlock2.res test-cases/parahip/disj-no-deadlock2.n

echo "======= parahip/disj-no-deadlock3.ss ======"
diff test-cases/parahip/disj-no-deadlock3.res test-cases/parahip/disj-no-deadlock3.n

echo "======= parahip/disj-deadlock.ss ======"
diff test-cases/parahip/disj-deadlock.res test-cases/parahip/disj-deadlock.n

echo "======= parahip/ordered-locking.ss ======"
diff test-cases/parahip/ordered-locking.res test-cases/parahip/ordered-locking.n

echo "======= parahip/unordered-locking.ss ======"
diff test-cases/parahip/unordered-locking.res test-cases/parahip/unordered-locking.n

# echo "======= parahip/multicast.ss ======"
# ##No Fork/Join
# diff test-cases/parahip/multicast.res test-cases/parahip/multicast.n

echo "======= parahip/oracle.ss ======"
diff test-cases/parahip/oracle.res test-cases/parahip/oracle.n

echo "======= parahip/owicki-gries.ss ======"
diff test-cases/parahip/owicki-gries.res test-cases/parahip/owicki-gries.n

echo "======= parahip/fibonacci.ss ======"
diff test-cases/parahip/fibonacci.res test-cases/parahip/fibonacci.n

# echo "======= parahip/create_and_acquire.ss ======"
# ##No Fork/Join
# diff test-cases/parahip/create_and_acquire.res test-cases/parahip/create_and_acquire.n

#================BENCHMARK==========================
#================BENCHMARK==========================
