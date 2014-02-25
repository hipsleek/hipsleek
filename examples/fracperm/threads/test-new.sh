# create a list of new results
# ================SLEEK==========================
# ================SLEEK==========================
echo "======= thrd1.slk ======"
../../../sleek --en-para --en-thrd-resource -tp redlog thrd1.slk | grep Entail > test-cases/thrd1.n

#================HIP==========================
#================HIP==========================
echo "======= motiv-example.ss  ======"
../../../hip --en-para --en-thrd-resource -tp redlog motiv-example.ss | grep -E 'Proc|assert:' > test-cases/motiv-example.n
echo "======= motiv-example2.ss  ======"
../../../hip --en-para --en-thrd-resource -tp redlog motiv-example2.ss | grep -E 'Proc|assert:' > test-cases/motiv-example2.n

#================PARAHIP==========================
#================PARAHIP==========================
# echo "======= parahip/simple.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/simple.ss | grep -E 'Proc|assert:' > test-cases/parahip/simple.n
echo "======= parahip/forkjoin.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/forkjoin.ss | grep -E 'Proc|assert:' > test-cases/parahip/forkjoin.n
# echo "======= parahip/cell.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/cell.ss | grep -E 'Proc|assert:' > test-cases/parahip/cell.n
echo "======= parahip/cell4.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/cell4.ss | grep -E 'Proc|assert:' > test-cases/parahip/cell4.n
# echo "======= parahip/cell-lock-vperm.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/cell-lock-vperm.ss | grep -E 'Proc|assert:' > test-cases/parahip/cell-lock-vperm.n
echo "======= parahip/cell-extreme-cases.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/cell-extreme-cases.ss | grep -E 'Proc|assert:' > test-cases/parahip/cell-extreme-cases.n
echo "======= parahip/ls-bind.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/ls-bind.ss | grep -E 'Proc|assert:' > test-cases/parahip/ls-bind.n
# echo "======= parahip/ls-waitlevel2.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/ls-waitlevel2.ss | grep -E 'Proc|assert:' > test-cases/parahip/ls-waitlevel2.n
# echo "======= parahip/double-acquire.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/double-acquire.ss | grep -E 'Proc|assert:' > test-cases/parahip/double-acquire.n
echo "======= parahip/no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/parahip/no-deadlock1.n
echo "======= parahip/no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/parahip/no-deadlock2.n
echo "======= parahip/no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/parahip/no-deadlock3.n
echo "======= parahip/deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/deadlock1.ss | grep -E 'Proc|assert:' > test-cases/parahip/deadlock1.n
echo "======= parahip/deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/deadlock2.ss | grep -E 'Proc|assert:' > test-cases/parahip/deadlock2.n
echo "======= parahip/deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/deadlock3.ss | grep -E 'Proc|assert:' > test-cases/parahip/deadlock3.n
echo "======= parahip/disj-no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/disj-no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/parahip/disj-no-deadlock1.n
echo "======= parahip/disj-no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/disj-no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/parahip/disj-no-deadlock2.n
echo "======= parahip/disj-no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/disj-no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/parahip/disj-no-deadlock3.n
echo "======= parahip/disj-deadlock.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/disj-deadlock.ss | grep -E 'Proc|assert:' > test-cases/parahip/disj-deadlock.n
echo "======= parahip/ordered-locking.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/ordered-locking.ss | grep -E 'Proc|assert:' > test-cases/parahip/ordered-locking.n
echo "======= parahip/unordered-locking.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/unordered-locking.ss | grep -E 'Proc|assert:' > test-cases/parahip/unordered-locking.n
# echo "======= parahip/multicast.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/multicast.ss | grep -E 'Proc|assert:' > test-cases/parahip/multicast.n
echo "======= parahip/oracle.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/oracle.ss | grep -E 'Proc|assert:' > test-cases/parahip/oracle.n
echo "======= parahip/owicki-gries.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/owicki-gries.ss | grep -E 'Proc|assert:' > test-cases/parahip/owicki-gries.n
echo "======= parahip/fibonacci.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer parahip/fibonacci.ss | grep -E 'Proc|assert:' > test-cases/parahip/fibonacci.n
# echo "======= parahip/create_and_acquire.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --dis-locklevel parahip/create_and_acquire.ss | grep -E 'Proc|assert:' > test-cases/parahip/create_and_acquire.n
#================BENCHMARK==========================
#================BENCHMARK==========================

