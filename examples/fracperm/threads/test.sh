#create a list of expected results
#================SLEEK==========================
#================SLEEK==========================
echo "======= thrd1.slk ======"
../../../sleek --en-para --en-thrd-resource -tp redlog thrd1.slk | grep Entail > test-cases/thrd1.res
echo "======= thrd2.slk ======"
../../../sleek --en-para --en-thrd-resource -tp redlog thrd2.slk | grep Entail > test-cases/thrd2.res
echo "======= thrd-liveness.slk ======"
../../../sleek --en-para --en-thrd-resource -tp parahip thrd-liveness.slk | grep Entail > test-cases/thrd-liveness.slk.res

#================HIP==========================
#================HIP==========================
echo "======= thrd-liveness.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic thrd-liveness.ss | grep -E 'Proc|assert:' > test-cases/thrd-liveness.ss.res
echo "======= multi-join1.ss  ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/multi-join1.ss | grep -E 'Proc|assert:' > test-cases/multi-join1.res
echo "======= multi-join2.ss  ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/multi-join2.ss | grep -E 'Proc|assert:' > test-cases/multi-join2.res
echo "======= multi-join3.ss  ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/multi-join3.ss | grep -E 'Proc|assert:' > test-cases/multi-join3.res
echo "======= no-deadlock-nonlexical2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/no-deadlock-nonlexical2.ss | grep -E 'Proc|assert:' >  test-cases/no-deadlock-nonlexical2.res

echo "======= point.ss  ======"
../../../hip --en-para --en-thrd-resource --dis-locklevel -tp parahip --classic point.ss | grep -E 'Proc|assert:' >  test-cases/point.res

echo "======= frac-cell-list.ss  ======"
../../../hip --en-para -tp parahip --classic frac-cell-list.ss | grep -E 'Proc|assert:' >  test-cases/frac-cell-list.res

echo "======= threadpool.ss ======"
../../../hip --en-thrd-resource --en-para -tp parahip --en-lsmu-infer --dis-ls  --classic threadhip/threadpool.ss | grep -E 'Proc|assert:' >  test-cases/threadpool.res

echo "======= deadpool.ss ======"
../../../hip --en-thrd-resource --en-para -tp parahip --en-lsmu-infer --dis-ls  --classic threadhip/deadpool.ss | grep -E 'Proc|assert:' >  test-cases/deadpool.res

echo "======= multicast.ss ======"
../../../hip --en-thrd-resource --en-para -tp parahip --en-lsmu-infer --classic threadhip/multicast.ss | grep -E 'Proc|assert:' >  test-cases/multicast.res

#================PARAHIP==========================
#================PARAHIP==========================
# echo "======= threadhip/simple.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/simple.ss | grep -E 'Proc|assert:' > test-cases/threadhip/simple.res
echo "======= threadhip/forkjoin.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/others/forkjoin.ss | grep -E 'Proc|assert:' > test-cases/threadhip/forkjoin.res
# echo "======= threadhip/cell.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/cell.ss | grep -E 'Proc|assert:' > test-cases/threadhip/cell.res
echo "======= threadhip/cell4.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/others/cell4.ss | grep -E 'Proc|assert:' > test-cases/threadhip/cell4.res
# echo "======= threadhip/cell-lock-vperm.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/cell-lock-vperm.ss | grep -E 'Proc|assert:' > test-cases/threadhip/cell-lock-vperm.res
# echo "======= threadhip/cell-extreme-cases.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/cell-extreme-cases.ss | grep -E 'Proc|assert:' > test-cases/threadhip/cell-extreme-cases.res
echo "======= threadhip/ls-bind.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/others/ls-bind.ss | grep -E 'Proc|assert:' > test-cases/threadhip/ls-bind.res
# echo "======= threadhip/ls-waitlevel2.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer threadhip/ls-waitlevel2.ss | grep -E 'Proc|assert:' > test-cases/threadhip/ls-waitlevel2.res


echo "======= threadhip/double-acquire.ss ======"
##No Fork/Join
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/double-acquire.ss | grep -E 'Proc|assert:' > test-cases/threadhip/double-acquire.res
echo "======= threadhip/deadlock-nonlexical.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/deadlock-nonlexical.ss | grep -E 'Proc|assert:' >  test-cases/threadhip/deadlock-nonlexical.res
echo "======= threadhip/no-deadlock-nonlexical.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/no-deadlock-nonlexical.ss | grep -E 'Proc|assert:' >  test-cases/threadhip/no-deadlock-nonlexical.res
echo "======= threadhip/no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/threadhip/no-deadlock1.res
echo "======= threadhip/no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/threadhip/no-deadlock2.res
echo "======= threadhip/no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/threadhip/no-deadlock3.res
echo "======= threadhip/deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/deadlock1.ss | grep -E 'Proc|assert:' > test-cases/threadhip/deadlock1.res
echo "======= threadhip/deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/deadlock2.ss | grep -E 'Proc|assert:' > test-cases/threadhip/deadlock2.res
echo "======= threadhip/deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/deadlock3.ss | grep -E 'Proc|assert:' > test-cases/threadhip/deadlock3.res
echo "======= threadhip/deadlock-nested-forkjoin.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/deadlock-nested-forkjoin.ss | grep -E 'Proc|assert:' > test-cases/threadhip/deadlock-nested-forkjoin.res
echo "======= threadhip/fork-join-as-send-recv.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/fork-join-as-send-recv.ss | grep -E 'Proc|assert:' > test-cases/threadhip/fork-join-as-send-recv.res
echo "======= threadhip/disj-no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/disj-no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/threadhip/disj-no-deadlock1.res
echo "======= threadhip/disj-no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/disj-no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/threadhip/disj-no-deadlock2.res
echo "======= threadhip/disj-no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/disj-no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/threadhip/disj-no-deadlock3.res
echo "======= threadhip/disj-deadlock.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/disj-deadlock.ss | grep -E 'Proc|assert:' > test-cases/threadhip/disj-deadlock.res
echo "======= threadhip/ordered-locking.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/ordered-locking.ss | grep -E 'Proc|assert:' > test-cases/threadhip/ordered-locking.res
echo "======= threadhip/unordered-locking.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/parahip-benchmark/unordered-locking.ss | grep -E 'Proc|assert:' > test-cases/threadhip/unordered-locking.res



echo "======= threadhip/oracle.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/oracle.ss | grep -E 'Proc|assert:' > test-cases/threadhip/oracle.res
echo "======= threadhip/owicki-gries.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/owicki-gries.ss | grep -E 'Proc|assert:' > test-cases/threadhip/owicki-gries.res
echo "======= threadhip/fibonacci.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --en-lsmu-infer --classic threadhip/fibonacci.ss | grep -E 'Proc|assert:' > test-cases/threadhip/fibonacci.res
# echo "======= threadhip/create_and_acquire.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-resource -tp parahip --dis-locklevel threadhip/create_and_acquire.ss | grep -E 'Proc|assert:' > test-cases/threadhip/create_and_acquire.res
echo "======= threadhip/parallel-mergesort.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --dis-ls --dis-locklevel --classic threadhip/parallel-mergesort.ss | grep -E 'Proc|assert:' > test-cases/threadhip/parallel-mergesort.res
echo "======= threadhip/parallel-quicksort.ss ======"
../../../hip --en-para --en-thrd-resource -tp parahip --dis-ls --dis-locklevel --classic threadhip/parallel-quicksort.ss | grep -E 'Proc|assert:' > test-cases/threadhip/parallel-quicksort.res
#================BENCHMARK==========================
#================BENCHMARK==========================




#==========================================
###### PARAHIP
#==========================================
echo "======= parahip/double-acquire.ss ======"
##No Fork/Join
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/double-acquire.ss | grep -E 'Proc|assert:' > test-cases/parahip/double-acquire.res
echo "======= parahip/deadlock-nonlexical.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/deadlock-nonlexical.ss | grep -E 'Proc|assert:' >  test-cases/parahip/deadlock-nonlexical.res
echo "======= parahip/no-deadlock-nonlexical.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/no-deadlock-nonlexical.ss | grep -E 'Proc|assert:' >  test-cases/parahip/no-deadlock-nonlexical.res
echo "======= parahip/no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/parahip/no-deadlock1.res
echo "======= parahip/no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/parahip/no-deadlock2.res
echo "======= parahip/no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/parahip/no-deadlock3.res
echo "======= parahip/deadlock1.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/deadlock1.ss | grep -E 'Proc|assert:' > test-cases/parahip/deadlock1.res
echo "======= parahip/deadlock2.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/deadlock2.ss | grep -E 'Proc|assert:' > test-cases/parahip/deadlock2.res
echo "======= parahip/deadlock3.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/deadlock3.ss | grep -E 'Proc|assert:' > test-cases/parahip/deadlock3.res
echo "======= parahip/deadlock-nested-forkjoin.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/deadlock-nested-forkjoin.ss | grep -E 'Proc|assert:' > test-cases/parahip/deadlock-nested-forkjoin.res
echo "======= parahip/fork-join-as-send-recv.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/fork-join-as-send-recv.ss | grep -E 'Proc|assert:' > test-cases/parahip/fork-join-as-send-recv.res
echo "======= parahip/disj-no-deadlock1.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/disj-no-deadlock1.ss | grep -E 'Proc|assert:' > test-cases/parahip/disj-no-deadlock1.res
echo "======= parahip/disj-no-deadlock2.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/disj-no-deadlock2.ss | grep -E 'Proc|assert:' > test-cases/parahip/disj-no-deadlock2.res
echo "======= parahip/disj-no-deadlock3.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/disj-no-deadlock3.ss | grep -E 'Proc|assert:' > test-cases/parahip/disj-no-deadlock3.res
echo "======= parahip/disj-deadlock.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/disj-deadlock.ss | grep -E 'Proc|assert:' > test-cases/parahip/disj-deadlock.res
echo "======= parahip/ordered-locking.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/ordered-locking.ss | grep -E 'Proc|assert:' > test-cases/parahip/ordered-locking.res
echo "======= parahip/unordered-locking.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/parahip-benchmark/unordered-locking.ss | grep -E 'Proc|assert:' > test-cases/parahip/unordered-locking.res



echo "======= parahip/oracle.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/oracle.ss | grep -E 'Proc|assert:' > test-cases/parahip/oracle.res
echo "======= parahip/owicki-gries.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/owicki-gries.ss | grep -E 'Proc|assert:' > test-cases/parahip/owicki-gries.res
echo "======= parahip/fibonacci.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --en-lsmu-infer --classic parahip/fibonacci.ss | grep -E 'Proc|assert:' > test-cases/parahip/fibonacci.res
# echo "======= parahip/create_and_acquire.ss ======"
# ##No Fork/Join
# ../../../hip --en-para --en-thrd-and-conj -tp parahip --dis-locklevel parahip/create_and_acquire.ss | grep -E 'Proc|assert:' > test-cases/parahip/create_and_acquire.res
echo "======= parahip/parallel-mergesort.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --dis-ls --dis-locklevel --classic parahip/parallel-mergesort.ss | grep -E 'Proc|assert:' > test-cases/parahip/parallel-mergesort.res
echo "======= parahip/parallel-quicksort.ss ======"
../../../hip --en-para --en-thrd-and-conj -tp parahip --dis-ls --dis-locklevel --classic parahip/parallel-quicksort.ss | grep -E 'Proc|assert:' > test-cases/parahip/parallel-quicksort.res


