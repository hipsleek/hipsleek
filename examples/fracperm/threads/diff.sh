#Compare old result with new result
#================SLEEK==========================
#================SLEEK==========================
echo "======= thrd1.slk ======"
diff test-cases/thrd1.res test-cases/thrd1.n
echo "======= thrd2.slk ======"
diff test-cases/thrd2.res test-cases/thrd2.n

#================HIP==========================
#================HIP==========================
echo "======= multi-join1.ss  ======"
diff test-cases/multi-join1.res test-cases/multi-join1.n
echo "======= multi-join2.ss  ======"
diff test-cases/multi-join2.res test-cases/multi-join2.n
echo "======= no-deadlock-nonlexical2.ss ======"
diff test-cases/no-deadlock-nonlexical2.res test-cases/no-deadlock-nonlexical2.n
echo "======= point.ss  ======"
diff test-cases/point.res test-cases/point.n
echo "======= frac-cell-list.ss  ======"
diff test-cases/frac-cell-list.res test-cases/frac-cell-list.n
echo "======= threadpool.ss ======"
diff test-cases/threadpool.res test-cases/threadpool.n
echo "======= multicast.ss ======"
diff test-cases/multicast.res test-cases/multicast.n

#================parahip-rsr/PARAHIP==========================
#================parahip-rsr/PARAHIP==========================
echo "======= parahip-rsr/no-deadlock-nonlexical.ss ======"
diff test-cases/parahip-rsr/no-deadlock-nonlexical.res test-cases/parahip-rsr/no-deadlock-nonlexical.n

# echo "======= parahip-rsr/simple.ss ======"
# ##No Fork/Join
# diff test-cases/parahip-rsr/simple.res test-cases/parahip-rsr/simple.n

echo "======= parahip-rsr/forkjoin.ss ======"
diff test-cases/parahip-rsr/forkjoin.res test-cases/parahip-rsr/forkjoin.n

# echo "======= parahip-rsr/cell.ss ======"
# ##No Fork/Join
# diff test-cases/parahip-rsr/cell.res test-cases/parahip-rsr/cell.n

echo "======= parahip-rsr/cell4.ss ======"
diff test-cases/parahip-rsr/cell4.res test-cases/parahip-rsr/cell4.n

# echo "======= parahip-rsr/cell-lock-vperm.ss ======"
# ##No Fork/Join
# diff test-cases/parahip-rsr/cell-lock-vperm.res test-cases/parahip-rsr/cell-lock-vperm.n

# echo "======= parahip-rsr/cell-extreme-cases.ss ======"
# ##No Fork/Join
# diff test-cases/parahip-rsr/cell-extreme-cases.res test-cases/parahip-rsr/cell-extreme-cases.n

echo "======= parahip-rsr/ls-bind.ss ======"
diff test-cases/parahip-rsr/ls-bind.res test-cases/parahip-rsr/ls-bind.n

# echo "======= parahip-rsr/ls-waitlevel2.ss ======"
# ##No Fork/Join
# diff test-cases/parahip-rsr/ls-waitlevel2.res test-cases/parahip-rsr/ls-waitlevel2.n

# echo "======= parahip-rsr/double-acquire.ss ======"
# ##No Fork/Join
# diff test-cases/parahip-rsr/double-acquire.res test-cases/parahip-rsr/double-acquire.n

echo "======= parahip-rsr/no-deadlock1.ss ======"
diff test-cases/parahip-rsr/no-deadlock1.res test-cases/parahip-rsr/no-deadlock1.n

echo "======= parahip-rsr/no-deadlock2.ss ======"
diff test-cases/parahip-rsr/no-deadlock2.res test-cases/parahip-rsr/no-deadlock2.n

echo "======= parahip-rsr/no-deadlock3.ss ======"
diff test-cases/parahip-rsr/no-deadlock3.res test-cases/parahip-rsr/no-deadlock3.n

echo "======= parahip-rsr/deadlock1.ss ======"
diff test-cases/parahip-rsr/deadlock1.res test-cases/parahip-rsr/deadlock1.n

echo "======= parahip-rsr/deadlock2.ss ======"
diff test-cases/parahip-rsr/deadlock2.res test-cases/parahip-rsr/deadlock2.n

echo "======= parahip-rsr/deadlock3.ss ======"
diff test-cases/parahip-rsr/deadlock3.res test-cases/parahip-rsr/deadlock3.n

echo "======= parahip-rsr/disj-no-deadlock1.ss ======"
diff test-cases/parahip-rsr/disj-no-deadlock1.res test-cases/parahip-rsr/disj-no-deadlock1.n

echo "======= parahip-rsr/disj-no-deadlock2.ss ======"
diff test-cases/parahip-rsr/disj-no-deadlock2.res test-cases/parahip-rsr/disj-no-deadlock2.n

echo "======= parahip-rsr/disj-no-deadlock3.ss ======"
diff test-cases/parahip-rsr/disj-no-deadlock3.res test-cases/parahip-rsr/disj-no-deadlock3.n

echo "======= parahip-rsr/disj-deadlock.ss ======"
diff test-cases/parahip-rsr/disj-deadlock.res test-cases/parahip-rsr/disj-deadlock.n

echo "======= parahip-rsr/ordered-locking.ss ======"
diff test-cases/parahip-rsr/ordered-locking.res test-cases/parahip-rsr/ordered-locking.n

echo "======= parahip-rsr/unordered-locking.ss ======"
diff test-cases/parahip-rsr/unordered-locking.res test-cases/parahip-rsr/unordered-locking.n

# echo "======= parahip-rsr/multicast.ss ======"
# ##No Fork/Join
# diff test-cases/parahip-rsr/multicast.res test-cases/parahip-rsr/multicast.n

echo "======= parahip-rsr/oracle.ss ======"
diff test-cases/parahip-rsr/oracle.res test-cases/parahip-rsr/oracle.n

echo "======= parahip-rsr/owicki-gries.ss ======"
diff test-cases/parahip-rsr/owicki-gries.res test-cases/parahip-rsr/owicki-gries.n

echo "======= parahip-rsr/fibonacci.ss ======"
diff test-cases/parahip-rsr/fibonacci.res test-cases/parahip-rsr/fibonacci.n

# echo "======= parahip-rsr/create_and_acquire.ss ======"
# ##No Fork/Join
# diff test-cases/parahip-rsr/create_and_acquire.res test-cases/parahip-rsr/create_and_acquire.n

#================BENCHMARK==========================
#================BENCHMARK==========================
