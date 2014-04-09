# create a list of new results
# ================SLEEK==========================
# ================SLEEK==========================
echo "======= thrd1.slk ======"
../../../sleek --en-para --en-thrd-resource -tp redlog thrd1.slk | grep Entail > test-cases/thrd1.n
echo "======= thrd2.slk ======"
../../../sleek --en-para --en-thrd-resource -tp redlog thrd2.slk | grep Entail > test-cases/thrd2.n

#================HIP==========================
#================HIP==========================
echo "======= multi-join1.ss  ======"
../../../hip --en-para --en-thrd-resource -tp redlog multi-join1.ss | grep -E 'Proc|assert:' > test-cases/multi-join1.n

echo "======= multi-join2.ss  ======"
../../../hip --en-para --en-thrd-resource -tp redlog multi-join2.ss | grep -E 'Proc|assert:' > test-cases/multi-join2.n

echo "======= no-deadlock-nonlexical2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer no-deadlock-nonlexical2.ss | grep -E 'Proc|assert:' >  test-cases/no-deadlock-nonlexical2.n

echo "======= point.ss  ======"
../../../hip --en-para --en-thrd-resource --dis-locklevel -tp parahip point.ss | grep -E 'Proc|assert:' >  test-cases/point.n

echo "======= frac-cell-list.ss  ======"
../../../hip --en-para -tp redlog frac-cell-list.ss | grep -E 'Proc|assert:' >  test-cases/frac-cell-list.n

echo "======= threadpool.ss ======"
../../../hip --en-thrd-resource --en-para -tp parahip --en-lsmu-infer threadpool.ss | grep -E 'Proc|assert:' >  test-cases/threadpool.n

echo "======= multicast.ss ======"
../../../hip --en-thrd-resource --en-para -tp parahip --en-lsmu-infer multicast.ss | grep -E 'Proc|assert:' >  test-cases/multicast.n

#================PARAHIP==========================
#================PARAHIP==========================
echo "======= threadhip/no-deadlock-nonlexical.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/no-deadlock-nonlexical.ss | grep -E 'Proc|assert:' >  test-cases/threadhip/no-deadlock-nonlexical.n
# echo "======= threadhip/simple.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/simple.ss | grep -E 'Proc|assert:' > test-cases/threadhip/simple.n
echo "======= threadhip/forkjoin.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/forkjoin.ss | grep -E 'Proc|assert:' > test-cases/threadhip/forkjoin.n
# echo "======= threadhip/cell.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/cell.ss | grep -E 'Proc|assert:' > test-cases/threadhip/cell.n
echo "======= threadhip/cell4.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/cell4.ss | grep -E 'Proc|assert:' > test-cases/threadhip/cell4.n
# echo "======= threadhip/cell-lock-vperm.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/cell-lock-vperm.ss | grep -E 'Proc|assert:' > test-cases/threadhip/cell-lock-vperm.n
echo "======= threadhip/cell-extreme-cases.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/cell-extreme-cases.ss | grep -E 'Proc|assert:' > test-cases/threadhip/cell-extreme-cases.n
echo "======= threadhip/ls-bind.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/ls-bind.ss | grep -E 'Proc|assert:' > test-cases/threadhip/ls-bind.n
# echo "======= threadhip/ls-waitlevel2.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/ls-waitlevel2.ss | grep -E 'Proc|assert:' > test-cases/threadhip/ls-waitlevel2.n
# echo "======= threadhip/double-acquire.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/double-acquire.ss | grep -E 'Proc|assert:' > test-cases/threadhip/double-acquire.n
echo "======= threadhip/no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/threadhip/no-deadlock1.n
echo "======= threadhip/no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/threadhip/no-deadlock2.n
echo "======= threadhip/no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/threadhip/no-deadlock3.n
echo "======= threadhip/deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/deadlock1.ss | grep -E 'Proc|assert:' > test-cases/threadhip/deadlock1.n
echo "======= threadhip/deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/deadlock2.ss | grep -E 'Proc|assert:' > test-cases/threadhip/deadlock2.n
echo "======= threadhip/deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/deadlock3.ss | grep -E 'Proc|assert:' > test-cases/threadhip/deadlock3.n
echo "======= threadhip/disj-no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/disj-no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/threadhip/disj-no-deadlock1.n
echo "======= threadhip/disj-no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/disj-no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/threadhip/disj-no-deadlock2.n
echo "======= threadhip/disj-no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/disj-no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/threadhip/disj-no-deadlock3.n
echo "======= threadhip/disj-deadlock.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/disj-deadlock.ss | grep -E 'Proc|assert:' > test-cases/threadhip/disj-deadlock.n
echo "======= threadhip/ordered-locking.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/ordered-locking.ss | grep -E 'Proc|assert:' > test-cases/threadhip/ordered-locking.n
echo "======= threadhip/unordered-locking.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/unordered-locking.ss | grep -E 'Proc|assert:' > test-cases/threadhip/unordered-locking.n
# echo "======= threadhip/multicast.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/multicast.ss | grep -E 'Proc|assert:' > test-cases/threadhip/multicast.n
echo "======= threadhip/oracle.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/oracle.ss | grep -E 'Proc|assert:' > test-cases/threadhip/oracle.n
echo "======= threadhip/owicki-gries.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/owicki-gries.ss | grep -E 'Proc|assert:' > test-cases/threadhip/owicki-gries.n
echo "======= threadhip/fibonacci.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/fibonacci.ss | grep -E 'Proc|assert:' > test-cases/threadhip/fibonacci.n
# echo "======= threadhip/create_and_acquire.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --dis-locklevel threadhip/create_and_acquire.ss | grep -E 'Proc|assert:' > test-cases/threadhip/create_and_acquire.n
#================BENCHMARK==========================
#================BENCHMARK==========================

