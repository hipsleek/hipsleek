#create a list of expected results
#================SLEEK==========================
#================SLEEK==========================
echo "======= thrd1.slk ======"
../../../sleek --en-para --en-thrd-resource -tp redlog thrd1.slk | grep Entail > test-cases/thrd1.res
echo "======= thrd2.slk ======"
../../../sleek --en-para --en-thrd-resource -tp redlog thrd2.slk | grep Entail > test-cases/thrd2.res
#================HIP==========================
#================HIP==========================
echo "======= multi-join1.ss  ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/multi-join1.ss | grep -E 'Proc|assert:' > test-cases/multi-join1.res
echo "======= multi-join2.ss  ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/multi-join2.ss | grep -E 'Proc|assert:' > test-cases/multi-join2.res
echo "======= no-deadlock-nonlexical2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/no-deadlock-nonlexical2.ss | grep -E 'Proc|assert:' >  test-cases/no-deadlock-nonlexical2.res

echo "======= point.ss  ======"
../../../hip --en-para --en-thrd-resource --dis-locklevel -tp parahip point.ss | grep -E 'Proc|assert:' >  test-cases/point.res

echo "======= frac-cell-list.ss  ======"
../../../hip --en-para -tp redlog frac-cell-list.ss | grep -E 'Proc|assert:' >  test-cases/frac-cell-list.res

echo "======= threadpool.ss ======"
../../../hip --en-thrd-resource --en-para -tp parahip --en-lsmu-infer threadhip/threadpool.ss | grep -E 'Proc|assert:' >  test-cases/threadpool.res

echo "======= multicast.ss ======"
../../../hip --en-thrd-resource --en-para -tp parahip --en-lsmu-infer threadhip/multicast.ss | grep -E 'Proc|assert:' >  test-cases/multicast.res

#================PARAHIP==========================
#================PARAHIP==========================
echo "======= threadhip/no-deadlock-nonlexical.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/no-deadlock-nonlexical.ss | grep -E 'Proc|assert:' >  test-cases/threadhip/no-deadlock-nonlexical.res
# echo "======= threadhip/simple.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/simple.ss | grep -E 'Proc|assert:' > test-cases/threadhip/simple.res
echo "======= threadhip/forkjoin.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/others/forkjoin.ss | grep -E 'Proc|assert:' > test-cases/threadhip/forkjoin.res
# echo "======= threadhip/cell.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/cell.ss | grep -E 'Proc|assert:' > test-cases/threadhip/cell.res
echo "======= threadhip/cell4.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/others/cell4.ss | grep -E 'Proc|assert:' > test-cases/threadhip/cell4.res
# echo "======= threadhip/cell-lock-vperm.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/cell-lock-vperm.ss | grep -E 'Proc|assert:' > test-cases/threadhip/cell-lock-vperm.res
# echo "======= threadhip/cell-extreme-cases.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/cell-extreme-cases.ss | grep -E 'Proc|assert:' > test-cases/threadhip/cell-extreme-cases.res
echo "======= threadhip/ls-bind.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/others/ls-bind.ss | grep -E 'Proc|assert:' > test-cases/threadhip/ls-bind.res
# echo "======= threadhip/ls-waitlevel2.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/ls-waitlevel2.ss | grep -E 'Proc|assert:' > test-cases/threadhip/ls-waitlevel2.res
# echo "======= threadhip/double-acquire.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/double-acquire.ss | grep -E 'Proc|assert:' > test-cases/threadhip/double-acquire.res
echo "======= threadhip/no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/threadhip/no-deadlock1.res
echo "======= threadhip/no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/threadhip/no-deadlock2.res
echo "======= threadhip/no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/threadhip/no-deadlock3.res
echo "======= threadhip/deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/deadlock1.ss | grep -E 'Proc|assert:' > test-cases/threadhip/deadlock1.res
echo "======= threadhip/deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/deadlock2.ss | grep -E 'Proc|assert:' > test-cases/threadhip/deadlock2.res
echo "======= threadhip/deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/deadlock3.ss | grep -E 'Proc|assert:' > test-cases/threadhip/deadlock3.res
echo "======= threadhip/disj-no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/disj-no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/threadhip/disj-no-deadlock1.res
echo "======= threadhip/disj-no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/disj-no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/threadhip/disj-no-deadlock2.res
echo "======= threadhip/disj-no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/disj-no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/threadhip/disj-no-deadlock3.res
echo "======= threadhip/disj-deadlock.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/disj-deadlock.ss | grep -E 'Proc|assert:' > test-cases/threadhip/disj-deadlock.res
echo "======= threadhip/ordered-locking.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/ordered-locking.ss | grep -E 'Proc|assert:' > test-cases/threadhip/ordered-locking.res
echo "======= threadhip/unordered-locking.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/parahip-benchmark/unordered-locking.ss | grep -E 'Proc|assert:' > test-cases/threadhip/unordered-locking.res
# echo "======= threadhip/multicast.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/multicast.ss | grep -E 'Proc|assert:' > test-cases/threadhip/multicast.res
echo "======= threadhip/oracle.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/oracle.ss | grep -E 'Proc|assert:' > test-cases/threadhip/oracle.res
echo "======= threadhip/owicki-gries.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/owicki-gries.ss | grep -E 'Proc|assert:' > test-cases/threadhip/owicki-gries.res
echo "======= threadhip/fibonacci.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/fibonacci.ss | grep -E 'Proc|assert:' > test-cases/threadhip/fibonacci.res
# echo "======= threadhip/create_and_acquire.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --dis-locklevel threadhip/create_and_acquire.ss | grep -E 'Proc|assert:' > test-cases/threadhip/create_and_acquire.res

#================BENCHMARK==========================
#================BENCHMARK==========================
