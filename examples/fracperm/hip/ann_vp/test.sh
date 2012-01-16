#create a list of expected results
echo "======= vperm2.ss ======"
../../../../hip vperm2.ss > vperm2.res
echo "======= vperm3.ss ======"
../../../../hip vperm3.ss > vperm3.res
echo "======= vperm4.ss ======"
../../../../hip vperm4.ss > vperm4.res
echo "======= vperm_check.ss ======"
../../../../hip vperm_check.ss > vperm_check.res
echo "======= parallelCount.ss ======"
../../../../hip parallelCount.ss > parallelCount.res
echo "======= parallel_merge_sort.ss ======"
../../../../hip parallel_merge_sort.ss > parallel_merge_sort.res
echo "======= parallel_quick_sort.ss ======"
../../../../hip parallel_quick_sort.ss > parallel_quick_sort.res
echo "======= alt_threading.ss ======"
../../../../hip alt_threading.ss > alt_threading.res
echo "======= threads.ss ======"
../../../../hip threads.ss > threads.res
echo "======= parallel_fibonacci.ss ======"
../../../../hip -tp z3 -perm none parallel_fibonacci.ss > parallel_fibonacci.res
