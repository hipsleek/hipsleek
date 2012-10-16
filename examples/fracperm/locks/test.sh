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
