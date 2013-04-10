#create a list of expected results
#================SLEEK==========================
#================SLEEK==========================
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
echo "======= barrier-sep.slk ======"
../../sleek barrier-sep.slk | grep Entail > test-cases/barrier-sep.res
echo "======= barrier-static.slk ======"
../../sleek barrier-static.slk | grep Entail > test-cases/barrier-static.res
echo "======= barrier-dynamic.slk ======"
../../sleek barrier-dynamic.slk | grep Entail > test-cases/barrier-dynamic.res
#================HIP==========================
#================HIP==========================
echo "======= hip-bperm1.ss ======"
../../hip hip-bperm1.ss | grep -E 'Proc|assert:' > test-cases/hip-bperm1.res
echo "======= bperm-exp.ss ======"
../../hip bperm-exp.ss | grep -E 'Proc|assert:' > test-cases/bperm-exp.res
echo "======= barrier-static-primitives.ss ======"
../../hip barrier-static-primitives.ss | grep -E 'Proc|assert:' > test-cases/barrier-static-primitives.res
echo "======= barrier-static-exp1.ss ======"
../../hip barrier-static-exp1.ss | grep -E 'Proc|assert:' > test-cases/barrier-static-exp1.res
echo "======= barrier-static-exp2.ss ======"
../../hip barrier-static-exp2.ss | grep -E 'Proc|assert:' > test-cases/barrier-static-exp2.res
echo "======= barrier-static-exp3.ss ======"
../../hip barrier-static-exp3.ss | grep -E 'Proc|assert:' > test-cases/barrier-static-exp3.res
echo "======= barrier-static-complex.ss ======"
../../hip barrier-static-complex.ss | grep -E 'Proc|assert:' > test-cases/barrier-static-complex.res
echo "======= barrier-static-complex2.ss ======"
../../hip barrier-static-complex2.ss | grep -E 'Proc|assert:' > test-cases/barrier-static-complex2.res
echo "======= barrier-static-multiple.ss ======"
../../hip barrier-static-multiple.ss | grep -E 'Proc|assert:' > test-cases/barrier-static-multiple.res
echo "======= barrier-dynamic-exp1.ss ======"
../../hip barrier-dynamic-exp1.ss | grep -E 'Proc|assert:' > test-cases/barrier-dynamic-exp1.res
echo "======= barrier-dynamic-exp2.ss ======"
../../hip barrier-dynamic-exp2.ss | grep -E 'Proc|assert:' > test-cases/barrier-dynamic-exp2.res
echo "======= barrier-dynamic-exp3.ss ======"
../../hip barrier-dynamic-exp3.ss | grep -E 'Proc|assert:' > test-cases/barrier-dynamic-exp3.res
#================BENCHMARK==========================
#================BENCHMARK==========================
echo "======= plash2/code/apps/barnes/ ======"
../../hip benchmark/our-splash2/code/apps/barnes/barnes.ss | grep -E 'Proc|assert:' > test-cases/splash2/barnes.res
echo "======= plash2/code/apps/fmm/ ======"
../../hip benchmark/our-splash2/code/apps/fmm/fmm.ss | grep -E 'Proc|assert:' > test-cases/splash2/fmm.res
echo "======= plash2/code/apps/ocean/ ======"
../../hip benchmark/our-splash2/code/apps/ocean/ocean.ss | grep -E 'Proc|assert:' > test-cases/splash2/ocean.res
echo "======= plash2/code/apps/raytrace/ ======"
../../hip benchmark/our-splash2/code/apps/raytrace/raytrace.ss | grep -E 'Proc|assert:' > test-cases/splash2/raytrace.res
echo "======= plash2/code/apps/volrend/ (slow) ======"
../../hip benchmark/our-splash2/code/apps/volrend/volrend.ss | grep -E 'Proc|assert:' > test-cases/splash2/volrend.res
echo "======= plash2/code/apps/water-nsquared/ (a bit slow) ======"
../../hip benchmark/our-splash2/code/apps/water-nsquared/water-nsquared.ss | grep -E 'Proc|assert:' > test-cases/splash2/water-nsquared.res
echo "======= plash2/code/apps/water-spatial/ (a bit slow) ======"
../../hip benchmark/our-splash2/code/apps/water-spatial/water-spatial.ss | grep -E 'Proc|assert:' > test-cases/splash2/water-spatial.res
echo "======= plash2/code/kernels/cholesky/ ======"
../../hip benchmark/our-splash2/code/kernels/cholesky/cholesky.ss | grep -E 'Proc|assert:' > test-cases/splash2/cholesky.res
echo "======= plash2/code/kernels/fft/ ======"
../../hip benchmark/our-splash2/code/kernels/fft/fft.ss | grep -E 'Proc|assert:' > test-cases/splash2/fft.res
