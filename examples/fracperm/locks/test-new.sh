#create a list of new results
echo "======= cell.ss ======"
../../../hip cell.ss | grep -E 'Proc|assert' > test-cases/cell.n
echo "======= cell4.ss ======"
../../../hip cell4.ss | grep -E 'Proc|assert' > test-cases/cell4.n
echo "======= cell-lock-vperm.ss ======"
../../../hip cell-lock-vperm.ss | grep -E 'Proc|assert' > test-cases/cell-lock-vperm.n
echo "======= cell-extreme-cases.ss ======"
../../../hip cell-extreme-cases.ss | grep -E 'Proc|assert' > test-cases/cell-extreme-cases.n
echo "======= ls-bind.ss ======"
../../../hip ls-bind.ss | grep -E 'Proc|assert' > test-cases/ls-bind.n

########### MOST IMPORTANT (rules + examples) ####################
echo "======= cell-w-ls.ss ======"
../../../hip cell-w-ls.ss | grep -E 'Proc|assert' > test-cases/cell-w-ls.n
echo "======= multicast.ss ======"
../../../hip multicast.ss | grep -E 'Proc|assert' > test-cases/multicast.n
