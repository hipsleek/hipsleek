#create a list of expected results
echo "======= cell.ss ======"
../../../hip cell.ss | grep -E 'Proc|assert' > test-cases/cell.res
echo "======= cell4.ss ======"
../../../hip cell4.ss | grep -E 'Proc|assert' > test-cases/cell4.res
echo "======= cell-lock-vperm.ss ======"
../../../hip cell-lock-vperm.ss | grep -E 'Proc|assert' > test-cases/cell-lock-vperm.res
echo "======= cell-extreme-cases.ss ======"
../../../hip cell-extreme-cases.ss | grep -E 'Proc|assert' > test-cases/cell-extreme-cases.res
echo "======= ls-bind.ss ======"
../../../hip ls-bind.ss | grep -E 'Proc|assert' > test-cases/ls-bind.res

########### MOST IMPORTANT (rules + examples) ####################
echo "======= cell-w-ls.ss ======"
../../../hip cell-w-ls.ss | grep -E 'Proc|assert' > test-cases/cell-w-ls.res
echo "======= multicast.ss ======"
../../../hip multicast.ss | grep -E 'Proc|assert' > test-cases/multicast.res
echo "======= oracle-esop08.ss ======"
../../../hip oracle-esop08.ss | grep -E 'Proc|assert' > test-cases/oracle-esop08.res
echo "======= owicki-gries.ss ======"
../../../hip owicki-gries.ss | grep -E 'Proc|assert' > test-cases/owicki-gries.res

########### Example of verifying deadlock freedom ####################
echo "======= ls-deadlock1.ss ======"
../../../hip ls-deadlock1.ss | grep -E 'Proc|assert' > test-cases/ls-deadlock1.res
echo "======= ls-deadlock2.ss ======"
../../../hip ls-deadlock2.ss | grep -E 'Proc|assert' > test-cases/ls-deadlock2.res
echo "======= ls-deadlock3.ss ======"
../../../hip ls-deadlock3.ss | grep -E 'Proc|assert' > test-cases/ls-deadlock3.res
echo "======= ls-double-acquisition.ss ======"
../../../hip ls-double-acquisition.ss | grep -E 'Proc|assert' > test-cases/ls-double-acquisition.res

echo "======= ls-no-deadlock1.ss ======"
../../../hip ls-no-deadlock1.ss | grep -E 'Proc|assert' > test-cases/ls-no-deadlock1.res
echo "======= ls-no-deadlock2.ss ======"
../../../hip ls-no-deadlock2.ss | grep -E 'Proc|assert' > test-cases/ls-no-deadlock2.res
echo "======= ls-no-deadlock3.ss ======"
../../../hip ls-no-deadlock3.ss | grep -E 'Proc|assert' > test-cases/ls-no-deadlock3.res

######## Example of verifying deadlock freedom with disjunction########
echo "======= ls-disj-deadlock.ss ======"
../../../hip ls-disj-deadlock.ss | grep -E 'Proc|assert' > test-cases/ls-disj-deadlock.res

echo "======= ls-disj-no-deadlock.ss ======"
../../../hip ls-disj-no-deadlock.ss | grep -E 'Proc|assert' > test-cases/ls-disj-no-deadlock.res
echo "======= ls-disj-no-deadlock2.ss ======"
../../../hip ls-disj-no-deadlock2.ss | grep -E 'Proc|assert' > test-cases/ls-disj-no-deadlock2.res
echo "======= ls-disj-no-deadlock3.ss ======"
../../../hip ls-disj-no-deadlock3.ss | grep -E 'Proc|assert' > test-cases/ls-disj-no-deadlock3.res
