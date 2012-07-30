#Compare old result with new result
echo "======= cell.ss ======"
diff test-cases/cell.res test-cases/cell.n
echo "======= cell4.ss ======"
diff test-cases/cell4.res test-cases/cell4.n
echo "======= cell-lock-vperm.ss ======"
diff test-cases/cell-lock-vperm.res test-cases/cell-lock-vperm.n
echo "======= cell-extreme-cases.ss ======"
diff test-cases/cell-extreme-cases.res test-cases/cell-extreme-cases.n
