#create a list of expected results
echo "======= bperm1.slk ======"
../../sleek bperm1.slk | grep Entail > test-cases/bperm1.res
echo "======= bperm-split.slk ======"
../../sleek bperm-split.slk | grep Entail > test-cases/bperm-split.res
echo "======= bperm-combine.slk ======"
../../sleek bperm-combine.slk | grep Entail > test-cases/bperm-combine.res
echo "======= bperm-split-combine.slk ======"
../../sleek bperm-split-combine.slk | grep Entail > test-cases/bperm-split-combine.res
echo "======= barrier1.slk ======"
../../sleek barrier1.slk | grep Entail > test-cases/barrier1.res
echo "======= barrier-split.slk ======"
../../sleek barrier-split.slk | grep Entail > test-cases/barrier-split.res
echo "======= barrier-combine.slk ======"
../../sleek barrier-combine.slk | grep Entail > test-cases/barrier-combine.res
