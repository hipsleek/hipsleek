#Compare old result with new result
#================HEADER=======================
#================HEADER=======================
echo "======= barrier_static_header.ss ======"
diff test-cases/barrier_static_header.res test-cases/barrier_static_header.n
echo "======= barrier_dynamic_header.ss ======"
diff test-cases/barrier_dynamic_header.res test-cases/barrier_dynamic_header.n
#================IN PAPER=======================
#================IN PAPER=======================
echo "======= fig.4.ss ======"
diff test-cases/fig.4.res test-cases/fig.4.n
echo "======= fig.5a.ss ======"
diff test-cases/fig.5a.res test-cases/fig.5a.n
echo "======= fig.5b.ss ======"
diff test-cases/fig.5b.res test-cases/fig.5b.n
echo "======= fig.7.ss ======"
diff test-cases/fig.7.res test-cases/fig.7.n
echo "======= fig.9.ss ======"
diff test-cases/fig.9.res test-cases/fig.9.n
echo "======= fig.11.ss ======"
diff test-cases/fig.11.res test-cases/fig.11.n
echo "======= fig.12a.ss ======"
diff test-cases/fig.12a.res test-cases/fig.12a.n
echo "======= fig.12b.ss ======"
diff test-cases/fig.12b.res test-cases/fig.12b.n
#================STATIC=======================
#================STATIC=======================
echo "======= static-complex1.ss ======"
diff test-cases/static-complex1.res test-cases/static-complex1.n
echo "======= static-complex2.ss ======"
diff test-cases/static-complex2.res test-cases/static-complex2.n
#================DYNAMIC=======================
#================DYNAMIC=======================
echo "======= dynamic-1.ss ======"
diff test-cases/dynamic-1.res test-cases/dynamic-1.n
echo "======= dynamic-3.ss ======"
diff test-cases/dynamic-2.res test-cases/dynamic-2.n
echo "======= dynamic-3.ss ======"
diff test-cases/dynamic-3.res test-cases/dynamic-3.n
echo "======= dynamic-4.ss ======"
diff test-cases/dynamic-4.res test-cases/dynamic-4.n
echo "======= dynamic-5.ss ======"
diff test-cases/dynamic-5.res test-cases/dynamic-5.n
echo "======= dynamic-6.ss ======"
diff test-cases/dynamic-6.res test-cases/dynamic-6.n
