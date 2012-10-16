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
