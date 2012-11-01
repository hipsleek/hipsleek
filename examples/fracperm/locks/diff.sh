#Compare old result with new result
echo "======= cell.ss ======"
diff test-cases/cell.res test-cases/cell.n
echo "======= cell4.ss ======"
diff test-cases/cell4.res test-cases/cell4.n
echo "======= cell-lock-vperm.ss ======"
diff test-cases/cell-lock-vperm.res test-cases/cell-lock-vperm.n
echo "======= cell-extreme-cases.ss ======"
diff test-cases/cell-extreme-cases.res test-cases/cell-extreme-cases.n
echo "======= ls-bind.ss ======"
diff test-cases/ls-bind.res test-cases/ls-bind.n

########### MOST IMPORTANT (rules + examples) ####################
echo "======= cell-w-ls.ss ======"
diff test-cases/cell-w-ls.res test-cases/cell-w-ls.n
echo "======= multicast.ss ======"
diff test-cases/multicast.res test-cases/multicast.n
echo "======= oracle-esop08.ss ======"
diff test-cases/oracle-esop08.res test-cases/oracle-esop08.n
echo "======= owicki-gries.ss ======"
diff test-cases/owicki-gries.res test-cases/owicki-gries.n

########### Example of verifying deadlock freedom ####################
echo "======= ls-deadlock1.ss ======"
diff test-cases/ls-deadlock1.res test-cases/ls-deadlock1.n
echo "======= ls-deadlock2.ss ======"
diff test-cases/ls-deadlock2.res test-cases/ls-deadlock2.n
echo "======= ls-deadlock3.ss ======"
diff test-cases/ls-deadlock3.res test-cases/ls-deadlock3.n

echo "======= ls-double-acquisition.ss ======"
diff test-cases/ls-double-acquisition.res test-cases/ls-double-acquisition.n

echo "======= ls-no-deadlock1.ss ======"
diff test-cases/ls-no-deadlock1.res test-cases/ls-no-deadlock1.n
echo "======= ls-no-deadlock2.ss ======"
diff test-cases/ls-no-deadlock2.res test-cases/ls-no-deadlock2.n
echo "======= ls-no-deadlock3.ss ======"
diff test-cases/ls-no-deadlock3.res test-cases/ls-no-deadlock3.n

######## Example of verifying deadlock freedom with disjunction########
echo "======= ls-disj-deadlock.ss ======"
diff test-cases/ls-disj-deadlock.res test-cases/ls-disj-deadlock.n

echo "======= ls-disj-no-deadlock.ss ======"
diff test-cases/ls-disj-no-deadlock.res test-cases/ls-disj-no-deadlock.n
echo "======= ls-disj-no-deadlock2.ss ======"
diff test-cases/ls-disj-no-deadlock2.res test-cases/ls-disj-no-deadlock2.n
echo "======= ls-disj-no-deadlock3.ss ======"
diff test-cases/ls-disj-no-deadlock3.res test-cases/ls-disj-no-deadlock3.n

########### Example demonstrating locklevels ####################
echo "======= ls-waitlevel.ss ======" #GENERAL TEST
diff test-cases/ls-waitlevel.res test-cases/ls-waitlevel.n
echo "======= ls-waitlevel2.ss ======" #GENERAL TEST
diff test-cases/ls-waitlevel2.res test-cases/ls-waitlevel2.n
echo "======= ls-unordered-locking.ss ======"
diff test-cases/ls-unordered-locking.res test-cases/ls-unordered-locking.n
echo "======= ls-ordered-locking.ss ======"
diff test-cases/ls-ordered-locking.res test-cases/ls-ordered-locking.n

