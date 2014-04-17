#Compare old result with new result
#================SLEEK==========================
#================SLEEK==========================
echo "======= thrd1.slk ======"
diff test-cases/thrd1.res test-cases/thrd1.n
echo "======= thrd2.slk ======"
diff test-cases/thrd2.res test-cases/thrd2.n
echo "======= thrd-liveness.slk ======"
diff test-cases/thrd-liveness.slk.res test-cases/thrd-liveness.slk.n
echo "======= thrd-liveness.ss ======"
diff test-cases/thrd-liveness.ss.res test-cases/thrd-liveness.ss.n

#================HIP==========================
#================HIP==========================
echo "======= multi-join1.ss  ======"
diff test-cases/multi-join1.res test-cases/multi-join1.n
echo "======= multi-join2.ss  ======"
diff test-cases/multi-join2.res test-cases/multi-join2.n
echo "======= multi-join3.ss  ======"
diff test-cases/multi-join3.res test-cases/multi-join3.n
echo "======= no-deadlock-nonlexical2.ss ======"
diff test-cases/no-deadlock-nonlexical2.res test-cases/no-deadlock-nonlexical2.n
echo "======= point.ss  ======"
diff test-cases/point.res test-cases/point.n
echo "======= frac-cell-list.ss  ======"
diff test-cases/frac-cell-list.res test-cases/frac-cell-list.n
echo "======= threadpool.ss ======"
diff test-cases/threadpool.res test-cases/threadpool.n
echo "======= deadpool.ss ======"
diff test-cases/deadpool.res test-cases/deadpool.n
echo "======= multicast.ss ======"
diff test-cases/multicast.res test-cases/multicast.n

#================threadhip/PARAHIP==========================
#================threadhip/PARAHIP==========================
# echo "======= threadhip/simple.ss ======"
# ##No Fork/Join
# diff test-cases/threadhip/simple.res test-cases/threadhip/simple.n

echo "======= threadhip/forkjoin.ss ======"
diff test-cases/threadhip/forkjoin.res test-cases/threadhip/forkjoin.n

# echo "======= threadhip/cell.ss ======"
# ##No Fork/Join
# diff test-cases/threadhip/cell.res test-cases/threadhip/cell.n

echo "======= threadhip/cell4.ss ======"
diff test-cases/threadhip/cell4.res test-cases/threadhip/cell4.n

# echo "======= threadhip/cell-lock-vperm.ss ======"
# ##No Fork/Join
# diff test-cases/threadhip/cell-lock-vperm.res test-cases/threadhip/cell-lock-vperm.n

# echo "======= threadhip/cell-extreme-cases.ss ======"
# ##No Fork/Join
# diff test-cases/threadhip/cell-extreme-cases.res test-cases/threadhip/cell-extreme-cases.n

echo "======= threadhip/ls-bind.ss ======"
diff test-cases/threadhip/ls-bind.res test-cases/threadhip/ls-bind.n

# echo "======= threadhip/ls-waitlevel2.ss ======"
# ##No Fork/Join
# diff test-cases/threadhip/ls-waitlevel2.res test-cases/threadhip/ls-waitlevel2.n




echo "======= threadhip/double-acquire.ss ======"
##No Fork/Join
diff test-cases/threadhip/double-acquire.res test-cases/threadhip/double-acquire.n

echo "======= threadhip/deadlock-nonlexical.ss ======"
diff test-cases/threadhip/deadlock-nonlexical.res test-cases/threadhip/deadlock-nonlexical.n

echo "======= threadhip/no-deadlock-nonlexical.ss ======"
diff test-cases/threadhip/no-deadlock-nonlexical.res test-cases/threadhip/no-deadlock-nonlexical.n

echo "======= threadhip/no-deadlock1.ss ======"
diff test-cases/threadhip/no-deadlock1.res test-cases/threadhip/no-deadlock1.n

echo "======= threadhip/no-deadlock2.ss ======"
diff test-cases/threadhip/no-deadlock2.res test-cases/threadhip/no-deadlock2.n

echo "======= threadhip/no-deadlock3.ss ======"
diff test-cases/threadhip/no-deadlock3.res test-cases/threadhip/no-deadlock3.n

echo "======= threadhip/deadlock1.ss ======"
diff test-cases/threadhip/deadlock1.res test-cases/threadhip/deadlock1.n

echo "======= threadhip/deadlock2.ss ======"
diff test-cases/threadhip/deadlock2.res test-cases/threadhip/deadlock2.n

echo "======= threadhip/deadlock3.ss ======"
diff test-cases/threadhip/deadlock3.res test-cases/threadhip/deadlock3.n

echo "======= threadhip/deadlock-nested-forkjoin.ss ======"
diff test-cases/threadhip/deadlock-nested-forkjoin.res test-cases/threadhip/deadlock-nested-forkjoin.n

echo "======= threadhip/fork-join-as-send-recv.ss ======"
diff test-cases/threadhip/fork-join-as-send-recv.res test-cases/threadhip/fork-join-as-send-recv.n

echo "======= threadhip/disj-no-deadlock1.ss ======"
diff test-cases/threadhip/disj-no-deadlock1.res test-cases/threadhip/disj-no-deadlock1.n

echo "======= threadhip/disj-no-deadlock2.ss ======"
diff test-cases/threadhip/disj-no-deadlock2.res test-cases/threadhip/disj-no-deadlock2.n

echo "======= threadhip/disj-no-deadlock3.ss ======"
diff test-cases/threadhip/disj-no-deadlock3.res test-cases/threadhip/disj-no-deadlock3.n

echo "======= threadhip/disj-deadlock.ss ======"
diff test-cases/threadhip/disj-deadlock.res test-cases/threadhip/disj-deadlock.n

echo "======= threadhip/ordered-locking.ss ======"
diff test-cases/threadhip/ordered-locking.res test-cases/threadhip/ordered-locking.n

echo "======= threadhip/unordered-locking.ss ======"
diff test-cases/threadhip/unordered-locking.res test-cases/threadhip/unordered-locking.n

# echo "======= threadhip/multicast.ss ======"
# ##No Fork/Join
# diff test-cases/threadhip/multicast.res test-cases/threadhip/multicast.n

echo "======= threadhip/oracle.ss ======"
diff test-cases/threadhip/oracle.res test-cases/threadhip/oracle.n

echo "======= threadhip/owicki-gries.ss ======"
diff test-cases/threadhip/owicki-gries.res test-cases/threadhip/owicki-gries.n

echo "======= threadhip/fibonacci.ss ======"
diff test-cases/threadhip/fibonacci.res test-cases/threadhip/fibonacci.n

# echo "======= threadhip/create_and_acquire.ss ======"
# ##No Fork/Join
# diff test-cases/threadhip/create_and_acquire.res test-cases/threadhip/create_and_acquire.n

echo "======= threadhip/parallel-mergesort.ss ======"
diff test-cases/threadhip/parallel-mergesort.res test-cases/threadhip/parallel-mergesort.n

echo "======= threadhip/parallel-quicksort.ss ======"
diff test-cases/threadhip/parallel-quicksort.res test-cases/threadhip/parallel-quicksort.n

#================BENCHMARK==========================
#================BENCHMARK==========================







#==========================================
###### PARAHIP
#==========================================
echo "======= parahip/double-acquire.ss ======"
##No Fork/Join
diff test-cases/parahip/double-acquire.res test-cases/parahip/double-acquire.n

echo "======= parahip/deadlock-nonlexical.ss ======"
diff test-cases/parahip/deadlock-nonlexical.res test-cases/parahip/deadlock-nonlexical.n

echo "======= parahip/no-deadlock-nonlexical.ss ======"
diff test-cases/parahip/no-deadlock-nonlexical.res test-cases/parahip/no-deadlock-nonlexical.n

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

echo "======= parahip/deadlock-nested-forkjoin.ss ======"
diff test-cases/parahip/deadlock-nested-forkjoin.res test-cases/parahip/deadlock-nested-forkjoin.n

echo "======= parahip/fork-join-as-send-recv.ss ======"
diff test-cases/parahip/fork-join-as-send-recv.res test-cases/parahip/fork-join-as-send-recv.n

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

echo "======= parahip/parallel-mergesort.ss ======"
diff test-cases/parahip/parallel-mergesort.res test-cases/parahip/parallel-mergesort.n

echo "======= parahip/parallel-quicksort.ss ======"
diff test-cases/parahip/parallel-quicksort.res test-cases/parahip/parallel-quicksort.n
