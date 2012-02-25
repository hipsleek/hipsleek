#create a list of new results
echo "======= vperm2.ss ======"
../../../../hip vperm2.ss > vperm2.n
echo "======= vperm3.ss ======"
../../../../hip vperm3.ss > vperm3.n
echo "======= vperm4.ss ======"
../../../../hip vperm4.ss > vperm4.n
echo "======= vperm_check.ss ======"
../../../../hip vperm_check.ss > vperm_check.n
echo "======= parallelCount.ss ======"
../../../../hip parallelCount.ss > parallelCount.n
echo "======= parallelCount2.ss ======"
../../../../hip parallelCount2.ss > parallelCount2.n
echo "======= parallel_merge_sort.ss ======"
../../../../hip parallel_merge_sort.ss > parallel_merge_sort.n
echo "======= parallel_quick_sort.ss ======"
../../../../hip parallel_quick_sort.ss > parallel_quick_sort.n
echo "======= alt_threading.ss ======"
../../../../hip alt_threading.ss > alt_threading.n
echo "======= alt_threading1.ss ======"
../../../../hip alt_threading1.ss > alt_threading1.n
echo "======= threads.ss ======"
../../../../hip threads.ss > threads.n
echo "======= parallel_fibonacci.ss ======"
../../../../hip -tp z3 -perm none parallel_fibonacci.ss > parallel_fibonacci.n
echo "======= parallel_fibonacci2.ss ======"
../../../../hip -tp z3 -perm none parallel_fibonacci2.ss > parallel_fibonacci2.n
echo "======= parallel_fibonacci3.ss ======"
../../../../hip -tp z3 -perm none parallel_fibonacci3.ss > parallel_fibonacci3.n
echo "======= parallel_tree_search.ss ======"
../../../../hip parallel_tree_search.ss -tp mona -perm none > parallel_tree_search.n
