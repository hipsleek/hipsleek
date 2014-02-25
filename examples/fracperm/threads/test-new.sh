# create a list of new results
# ================SLEEK==========================
# ================SLEEK==========================
echo "======= thrd1.slk ======"
../../../sleek --en-para --en-thrd-resource -tp redlog thrd1.slk | grep Entail > test-cases/thrd1.n

#================HIP==========================
#================HIP==========================
echo "======= motiv-example.ss  ======"
../../../hip --en-para --en-thrd-resource -tp redlog motiv-example.ss | grep -E 'Proc|assert:' > test-cases/motiv-example.n
echo "======= motiv-example2.ss  ======"
../../../hip --en-para --en-thrd-resource -tp redlog motiv-example2.ss | grep -E 'Proc|assert:' > test-cases/motiv-example2.n
#================BENCHMARK==========================
#================BENCHMARK==========================

