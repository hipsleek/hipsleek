#create a list of expected results
#================HEADER=======================
#================HEADER=======================
echo "======= barrier_static_header.ss ======"
../../../hip barrier_static_header.ss | grep -E 'Proc|assert:|FAIL' > test-cases/barrier_static_header.res
echo "======= barrier_dynamic_header.ss ======"
../../../hip barrier_dynamic_header.ss | grep -E 'Proc|assert:|FAIL' > test-cases/barrier_dynamic_header.res
#================IN PAPER=======================
#================IN PAPER=======================
echo "======= fig.4.ss ======"
../../../hip fig.4.ss | grep -E 'Proc|assert:' > test-cases/fig.4.res
echo "======= fig.5a.ss ======"
../../../hip fig.5a.ss | grep -E 'Proc|assert:' > test-cases/fig.5a.res
echo "======= fig.5b.ss ======"
../../../hip fig.5b.ss | grep -E 'Proc|assert:' > test-cases/fig.5b.res
echo "======= fig.7.ss ======"
../../../hip fig.7.ss | grep -E 'Proc|assert:' > test-cases/fig.7.res
echo "======= fig.9.ss ======"
../../../hip fig.9.ss | grep -E 'Proc|assert:' > test-cases/fig.9.res
echo "======= fig.11.ss ======"
../../../hip fig.11.ss | grep -E 'Proc|assert:' > test-cases/fig.11.res
echo "======= fig.12a.ss ======"
../../../hip fig.12a.ss | grep -E 'Proc|assert:' > test-cases/fig.12a.res
echo "======= fig.12b.ss ======"
../../../hip fig.12b.ss | grep -E 'Proc|assert:' > test-cases/fig.12b.res
#================STATIC=======================
#================STATIC=======================
echo "======= static-complex1.ss ======"
../../../hip static-complex1.ss | grep -E 'Proc|assert:' > test-cases/static-complex1.res
echo "======= static-complex2.ss ======"
../../../hip static-complex2.ss | grep -E 'Proc|assert:' > test-cases/static-complex2.res
#================DYNAMIC=======================
#================DYNAMIC=======================
echo "======= dynamic-1.ss (a bit slow) ======"
../../../hip dynamic-1.ss | grep -E 'Proc|assert:' > test-cases/dynamic-1.res
echo "======= dynamic-2.ss ======"
../../../hip dynamic-2.ss | grep -E 'Proc|assert:' > test-cases/dynamic-2.res
echo "======= dynamic-3.ss ======"
../../../hip dynamic-3.ss | grep -E 'Proc|assert:' > test-cases/dynamic-3.res
echo "======= dynamic-4.ss (slow) ======"
../../../hip dynamic-4.ss | grep -E 'Proc|assert:' > test-cases/dynamic-4.res
echo "======= dynamic-5.ss ======"
../../../hip dynamic-5.ss | grep -E 'Proc|assert:' > test-cases/dynamic-5.res
echo "======= dynamic-6.ss ======"
../../../hip dynamic-6.ss | grep -E 'Proc|assert:' > test-cases/dynamic-6.res
