#Compare old result with new result
echo "======= bperm1.slk ======"
diff test-cases/bperm1.res test-cases/bperm1.n
echo "======= bperm-split.slk ======"
diff test-cases/bperm-split.res test-cases/bperm-split.n
echo "======= bperm-combine.slk ======"
diff test-cases/bperm-combine.res test-cases/bperm-combine.n
echo "======= bperm-split-combine.slk ======"
diff test-cases/bperm-split-combine.res test-cases/bperm-split-combine.n
echo "======= barrier1.slk ======"
diff test-cases/barrier1.res test-cases/barrier1.n
echo "======= barrier-split.slk ======"
diff test-cases/barrier-split.res test-cases/barrier-split.n
echo "======= barrier-combine.slk ======"
diff test-cases/barrier-combine.res test-cases/barrier-combine.n
