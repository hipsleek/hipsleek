# create a list of new results
# ================SLEEK==========================
# ================SLEEK==========================
echo "======= thrd1.slk ======"
../../../sleek --en-para --en-thrd-resource -tp redlog thrd1.slk | grep Entail > test-cases/thrd1.n
echo "======= thrd2.slk ======"
../../../sleek --en-para --en-thrd-resource -tp redlog thrd2.slk | grep Entail > test-cases/thrd2.n

#================HIP==========================
#================HIP==========================
echo "======= motiv-example.ss  ======"
../../../hip --en-para --en-thrd-resource -tp redlog motiv-example.ss | grep -E 'Proc|assert:' > test-cases/motiv-example.n

echo "======= motiv-example2.ss  ======"
../../../hip --en-para --en-thrd-resource -tp redlog motiv-example2.ss | grep -E 'Proc|assert:' > test-cases/motiv-example2.n

echo "======= no-deadlock-nonlexical2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer no-deadlock-nonlexical2.ss | grep -E 'Proc|assert:' >  test-cases/no-deadlock-nonlexical2.n

echo "======= point.ss  ======"
../../../hip --en-para --en-thrd-resource --dis-locklevel -tp parahip point.ss | grep -E 'Proc|assert:' >  test-cases/point.n

echo "======= frac-cell-list.ss  ======"
../../../hip --en-para -tp redlog frac-cell-list.ss | grep -E 'Proc|assert:' >  test-cases/frac-cell-list.n

echo "======= thread-pool.ss ======"
../../../hip --en-thrd-resource --en-para -tp parahip --en-lsmu-infer thread-pool.ss | grep -E 'Proc|assert:' >  test-cases/thread-pool.n

echo "======= multicast.ss ======"
../../../hip --en-thrd-resource --en-para -tp parahip --en-lsmu-infer multicast.ss | grep -E 'Proc|assert:' >  test-cases/multicast.n

#================PARAHIP==========================
#================PARAHIP==========================
echo "======= parahip-rsr/no-deadlock-nonlexical.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/no-deadlock-nonlexical.ss | grep -E 'Proc|assert:' >  test-cases/parahip-rsr/no-deadlock-nonlexical.n
# echo "======= parahip-rsr/simple.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/simple.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/simple.n
echo "======= parahip-rsr/forkjoin.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/forkjoin.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/forkjoin.n
# echo "======= parahip-rsr/cell.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/cell.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/cell.n
echo "======= parahip-rsr/cell4.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/cell4.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/cell4.n
# echo "======= parahip-rsr/cell-lock-vperm.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/cell-lock-vperm.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/cell-lock-vperm.n
echo "======= parahip-rsr/cell-extreme-cases.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/cell-extreme-cases.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/cell-extreme-cases.n
echo "======= parahip-rsr/ls-bind.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/ls-bind.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/ls-bind.n
# echo "======= parahip-rsr/ls-waitlevel2.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/ls-waitlevel2.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/ls-waitlevel2.n
# echo "======= parahip-rsr/double-acquire.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/double-acquire.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/double-acquire.n
echo "======= parahip-rsr/no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/no-deadlock1.n
echo "======= parahip-rsr/no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/no-deadlock2.n
echo "======= parahip-rsr/no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/no-deadlock3.n
echo "======= parahip-rsr/deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/deadlock1.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/deadlock1.n
echo "======= parahip-rsr/deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/deadlock2.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/deadlock2.n
echo "======= parahip-rsr/deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/deadlock3.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/deadlock3.n
echo "======= parahip-rsr/disj-no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/disj-no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/disj-no-deadlock1.n
echo "======= parahip-rsr/disj-no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/disj-no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/disj-no-deadlock2.n
echo "======= parahip-rsr/disj-no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/disj-no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/disj-no-deadlock3.n
echo "======= parahip-rsr/disj-deadlock.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/disj-deadlock.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/disj-deadlock.n
echo "======= parahip-rsr/ordered-locking.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/ordered-locking.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/ordered-locking.n
echo "======= parahip-rsr/unordered-locking.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/unordered-locking.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/unordered-locking.n
# echo "======= parahip-rsr/multicast.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/multicast.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/multicast.n
echo "======= parahip-rsr/oracle.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/oracle.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/oracle.n
echo "======= parahip-rsr/owicki-gries.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/owicki-gries.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/owicki-gries.n
echo "======= parahip-rsr/fibonacci.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/fibonacci.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/fibonacci.n
# echo "======= parahip-rsr/create_and_acquire.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --dis-locklevel parahip-rsr/create_and_acquire.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/create_and_acquire.n
#================BENCHMARK==========================
#================BENCHMARK==========================

