#create a list of expected results
#================SLEEK==========================
#================SLEEK==========================
echo "======= thrd1.slk ======"
../../../sleek --en-para --en-thrd-resource -tp redlog thrd1.slk | grep Entail > test-cases/thrd1.res
#================HIP==========================
#================HIP==========================
echo "======= motiv-example.ss  ======"
../../../hip --en-para --en-thrd-resource -tp redlog motiv-example.ss | grep -E 'Proc|assert:' > test-cases/motiv-example.res
echo "======= motiv-example2.ss  ======"
../../../hip --en-para --en-thrd-resource -tp redlog motiv-example2.ss | grep -E 'Proc|assert:' > test-cases/motiv-example2.res
echo "======= no-deadlock-nonlexical2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer no-deadlock-nonlexical2.ss | grep -E 'Proc|assert:' >  test-cases/no-deadlock-nonlexical2.res

echo "======= point.ss  ======"
../../../hip --en-para --en-thrd-resource --dis-locklevel -tp parahip point.ss | grep -E 'Proc|assert:' >  test-cases/point.res

echo "======= frac-cell-list.ss  ======"
../../../hip --en-para -tp redlog frac-cell-list.ss | grep -E 'Proc|assert:' >  test-cases/frac-cell-list.res

#================PARAHIP==========================
#================PARAHIP==========================
echo "======= parahip-rsr/no-deadlock-nonlexical.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/no-deadlock-nonlexical.ss | grep -E 'Proc|assert:' >  test-cases/parahip-rsr/no-deadlock-nonlexical.res
# echo "======= parahip-rsr/simple.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/simple.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/simple.res
echo "======= parahip-rsr/forkjoin.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/forkjoin.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/forkjoin.res
# echo "======= parahip-rsr/cell.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/cell.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/cell.res
echo "======= parahip-rsr/cell4.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/cell4.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/cell4.res
# echo "======= parahip-rsr/cell-lock-vperm.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/cell-lock-vperm.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/cell-lock-vperm.res
# echo "======= parahip-rsr/cell-extreme-cases.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/cell-extreme-cases.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/cell-extreme-cases.res
echo "======= parahip-rsr/ls-bind.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/ls-bind.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/ls-bind.res
# echo "======= parahip-rsr/ls-waitlevel2.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/ls-waitlevel2.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/ls-waitlevel2.res
# echo "======= parahip-rsr/double-acquire.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/double-acquire.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/double-acquire.res
echo "======= parahip-rsr/no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/no-deadlock1.res
echo "======= parahip-rsr/no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/no-deadlock2.res
echo "======= parahip-rsr/no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/no-deadlock3.res
echo "======= parahip-rsr/deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/deadlock1.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/deadlock1.res
echo "======= parahip-rsr/deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/deadlock2.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/deadlock2.res
echo "======= parahip-rsr/deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/deadlock3.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/deadlock3.res
echo "======= parahip-rsr/disj-no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/disj-no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/disj-no-deadlock1.res
echo "======= parahip-rsr/disj-no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/disj-no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/disj-no-deadlock2.res
echo "======= parahip-rsr/disj-no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/disj-no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/disj-no-deadlock3.res
echo "======= parahip-rsr/disj-deadlock.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/disj-deadlock.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/disj-deadlock.res
echo "======= parahip-rsr/ordered-locking.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/ordered-locking.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/ordered-locking.res
echo "======= parahip-rsr/unordered-locking.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/unordered-locking.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/unordered-locking.res
# echo "======= parahip-rsr/multicast.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/multicast.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/multicast.res
echo "======= parahip-rsr/oracle.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/oracle.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/oracle.res
echo "======= parahip-rsr/owicki-gries.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/owicki-gries.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/owicki-gries.res
echo "======= parahip-rsr/fibonacci.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip-rsr/fibonacci.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/fibonacci.res
# echo "======= parahip-rsr/create_and_acquire.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --dis-locklevel parahip-rsr/create_and_acquire.ss | grep -E 'Proc|assert:' > test-cases/parahip-rsr/create_and_acquire.res

#================BENCHMARK==========================
#================BENCHMARK==========================
