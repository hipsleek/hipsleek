#create a list of new results
echo "======= bperm1.slk ======"
../../sleek bperm1.slk > test-cases/bperm1.n
echo "======= bperm-split.slk ======"
../../sleek bperm-split.slk > test-cases/bperm-split.n
echo "======= bperm-combine.slk ======"
../../sleek bperm-combine.slk > test-cases/bperm-combine.n
