#create a list of expected results
echo "======= bperm1.slk ======"
../../sleek bperm1.slk > test-cases/bperm1.res
echo "======= bperm-split.slk ======"
../../sleek bperm-split.slk > test-cases/bperm-split.res
echo "======= bperm-combine.slk ======"
../../sleek bperm-combine.slk > test-cases/bperm-combine.res
echo "======= bperm-split-combine.slk ======"
../../sleek bperm-split-combine.slk > test-cases/bperm-split-combine.res
