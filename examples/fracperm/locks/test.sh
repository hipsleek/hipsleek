#create a list of expected results
echo "======= cell.ss ======"
../../../hip cell.ss > test-cases/cell.res
echo "======= cell4.ss ======"
../../../hip cell4.ss > test-cases/cell4.res
echo "======= cell-lock-vperm.ss ======"
../../../hip cell-lock-vperm.ss > test-cases/cell-lock-vperm.res
echo "======= cell-extreme-cases.ss ======"
../../../hip cell-extreme-cases.ss > test-cases/cell-extreme-cases.res
