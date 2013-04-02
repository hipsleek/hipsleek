#create a list of new results
echo "======= bperm1.slk ======"
../../sleek bperm1.slk | grep Entail > test-cases/bperm1.n
echo "======= bperm-split.slk ======"
../../sleek bperm-split.slk | grep Entail > test-cases/bperm-split.n
echo "======= bperm-combine.slk ======"
../../sleek bperm-combine.slk | grep Entail > test-cases/bperm-combine.n
echo "======= bperm-split-combine.slk ======"
../../sleek bperm-split-combine.slk | grep Entail > test-cases/bperm-split-combine.n
echo "======= barrier1.slk ======"
../../sleek barrier1.slk | grep Entail > test-cases/barrier1.n
echo "======= barrier-split.slk ======"
../../sleek barrier-split.slk | grep Entail > test-cases/barrier-split.n
echo "======= barrier-combine.slk ======"
../../sleek barrier-combine.slk | grep Entail > test-cases/barrier-combine.n
echo "======= barrier-sep.slk ======"
../../sleek barrier-sep.slk | grep Entail > test-cases/barrier-sep.n
echo "======= barrier-static.slk ======"
../../sleek barrier-static.slk | grep Entail > test-cases/barrier-static.n
