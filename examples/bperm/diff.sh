#Compare old result with new result
#================SLEEK==========================
#================SLEEK==========================
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
echo "======= barrier-sep.slk ======"
diff test-cases/barrier-sep.res test-cases/barrier-sep.n
echo "======= barrier-static.slk ======"
diff test-cases/barrier-static.res test-cases/barrier-static.n
echo "======= barrier-dynamic.slk ======"
diff test-cases/barrier-dynamic.res test-cases/barrier-dynamic.n
#================HIP==========================
#================HIP==========================
echo "======= hip-bperm1.ss ======"
diff test-cases/hip-bperm1.res test-cases/hip-bperm1.n
echo "======= bperm-exp.ss ======"
diff test-cases/bperm-exp.res test-cases/bperm-exp.n
echo "======= barrier-static-primitives.ss ======"
diff test-cases/barrier-static-primitives.res test-cases/barrier-static-primitives.n
echo "======= barrier-static-exp1.ss ======"
diff test-cases/barrier-static-exp1.res test-cases/barrier-static-exp1.n
echo "======= barrier-static-exp2.ss ======"
diff test-cases/barrier-static-exp2.res test-cases/barrier-static-exp2.n
echo "======= barrier-static-exp3.ss ======"
diff test-cases/barrier-static-exp3.res test-cases/barrier-static-exp3.n
echo "======= barrier-static-complex.ss ======"
diff test-cases/barrier-static-complex.res test-cases/barrier-static-complex.n
echo "======= barrier-dynamic-exp1.ss ======"
diff test-cases/barrier-dynamic-exp1.res test-cases/barrier-dynamic-exp1.n
echo "======= barrier-dynamic-exp2.ss ======"
diff test-cases/barrier-dynamic-exp2.res test-cases/barrier-dynamic-exp2.n
echo "======= barrier-dynamic-exp3.ss ======"
diff test-cases/barrier-dynamic-exp3.res test-cases/barrier-dynamic-exp3.n
