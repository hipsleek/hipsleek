#create a list of new results
echo "======= vperm2.ss ======"
../../../../hip --ann-vp vperm2.ss > vperm2.n
echo "======= vperm3.ss ======"
../../../../hip --ann-vp vperm3.ss > vperm3.n
echo "======= vperm4.ss ======"
../../../../hip --ann-vp vperm4.ss > vperm4.n
echo "======= vperm_check.ss ======"
../../../../hip --ann-vp vperm_check.ss > vperm_check.n
echo "======= parallelCount.ss ======"
../../../../hip --ann-vp parallelCount.ss > parallelCount.n
echo "======= parallelCount2.ss ======"
../../../../hip --ann-vp parallelCount2.ss > parallelCount2.n
echo "======= parallel_merge_sort.ss ======"
../../../../hip --ann-vp parallel_merge_sort.ss > parallel_merge_sort.n
echo "======= parallel_quick_sort.ss ======"
../../../../hip --ann-vp parallel_quick_sort.ss > parallel_quick_sort.n
echo "======= alt_threading.ss ======"
../../../../hip --ann-vp alt_threading.ss > alt_threading.n
echo "======= alt_threading1.ss ======"
../../../../hip --ann-vp alt_threading1.ss > alt_threading1.n
echo "======= threads.ss ======"
../../../../hip --ann-vp threads.ss > threads.n
echo "======= parallel_fibonacci.ss ======"
../../../../hip --ann-vp -tp z3 -perm none parallel_fibonacci.ss > parallel_fibonacci.n
echo "======= parallel_fibonacci2.ss ======"
../../../../hip --ann-vp -tp z3 -perm none parallel_fibonacci2.ss > parallel_fibonacci2.n
echo "======= parallel_fibonacci3.ss ======"
../../../../hip --ann-vp -tp z3 -perm none parallel_fibonacci3.ss > parallel_fibonacci3.n
echo "======= parallel_tree_search.ss ======"
../../../../hip --ann-vp parallel_tree_search.ss -tp mona -perm none > parallel_tree_search.n
