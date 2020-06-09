Starting sleek-hip tests:
Starting hip tests:
Checking eps.ss
Checking append.ss
Checking append-tail.ss
Checking avl-bind.ss
Checking avl.ss
Checking avl-orig-2.ss
Checking avl-orig3.ss
Checking bll.ss
Checking bubble.ss
Checking cll.ss
Checking complete.ss
Checking dll.ss
Checking heaps.ss
Checking insertion.ss
Checking ll.ss
Checking merge.ss
Checking perfect.ss
Checking qsort.ss
Checking selection.ss
Checking sll.ss
Checking trees.ss
Checking rb.ss
Checking global1.ss
Checking global2.ss
Checking global3.ss
Checking global4.ss
Checking global5.ss
Checking global-ll.ss
Checking global-mutual-rec.ss
Checking classic/classic1.ss
Checking classic/classic1.ss (runs with extra options: --classic)
Checking classic/classic1a.ss
Checking classic/classic1a.ss (runs with extra options: --classic)
Checking classic/classic2.ss
Checking classic/classic2a.ss
Checking classic/classic3.ss
Checking classic/classic3a.ss
Checking ../../modular_examples/dll-modular.ss (runs with extra options: --overeps)
Checking ../../modular_examples/selection-modular.ss (runs with extra options: --overeps --lda)
Checking ../../modular_examples/qsort-modular.ss (runs with extra options: --overeps --lda)
Checking vperm/ho_vperm_check.ss (runs with extra options: --ann-vp)
Checking vperm/task_decompose.ss (runs with extra options: --ann-vp)
error at: vperm/task_decompose.ss inc
Checking parahip/cell.ss (runs with extra options: --en-para -tp parahip --en-lsmu-infer --en-thrd-and-conj)
error at: parahip/cell.ss test
Checking parahip/cell-extreme-cases.ss (runs with extra options: --en-para -tp parahip --en-lsmu-infer --en-thrd-and-conj)
Checking parahip/ordered-locking.ss (runs with extra options: --en-para -tp parahip --en-lsmu-infer --en-thrd-and-conj)
error at: parahip/ordered-locking.ss func
error at: parahip/ordered-locking.ss main
Checking parahip/unordered-locking.ss (runs with extra options: --en-para -tp parahip --en-lsmu-infer --en-thrd-and-conj)
error at: parahip/unordered-locking.ss main
Checking veribsync/hip-bperm1.ss (runs with extra options: --en-para -perm bperm -tp redlog)
error at: veribsync/hip-bperm1.ss readCell
error at: veribsync/hip-bperm1.ss updateCell
Checking veribsync/barrier-static-consistency.ss (runs with extra options: --en-para -perm bperm -tp redlog)
error at: veribsync/barrier-static-consistency.ss main_fail
Checking veribsync/barrier-dynamic-exp3.ss (runs with extra options: --en-para -perm bperm -tp redlog)
Checking veribsync/barrier-dynamic-exp4.ss (runs with extra options: --en-para -perm bperm -tp redlog)
Checking conchip/mapreduce.ss (runs with extra options: -tp parahip --classic)
error at: conchip/mapreduce.ss count_helper
error at: conchip/mapreduce.ss countList
error at: conchip/mapreduce.ss destroyList
error at: conchip/mapreduce.ss main
error at: conchip/mapreduce.ss mapper_helper
error at: conchip/mapreduce.ss mapper
error at: conchip/mapreduce.ss reducer1
error at: conchip/mapreduce.ss reducer2
Checking conchip/multi-join2.ss (runs with extra options: -tp parahip  -perm fperm --classic)
error at: conchip/multi-join2.ss main
error at: conchip/multi-join2.ss thread1
error at: conchip/multi-join2.ss thread2
Checking conchip/latch-exp2.ss (runs with extra options: -tp parahip --classic)
error at: conchip/latch-exp2.ss main
error at: conchip/latch-exp2.ss thread1
Checking conchip/deadpool.ss (runs with extra options: -tp parahip -perm fperm --classic)
error at: conchip/deadpool.ss destroyDeadPool
error at: conchip/deadpool.ss forkHelper
error at: conchip/deadpool.ss forkThreads
error at: conchip/deadpool.ss joinHelper
error at: conchip/deadpool.ss joinThreads
error at: conchip/deadpool.ss main
error at: conchip/deadpool.ss thread
Total number of errors: 28 in files:
 error at: vperm/task_decompose.ss inc
error at: parahip/cell.ss test
error at: parahip/ordered-locking.ss func
error at: parahip/ordered-locking.ss main
error at: parahip/unordered-locking.ss main
error at: veribsync/hip-bperm1.ss readCell
error at: veribsync/hip-bperm1.ss updateCell
error at: veribsync/barrier-static-consistency.ss main_fail
error at: conchip/mapreduce.ss count_helper
error at: conchip/mapreduce.ss countList
error at: conchip/mapreduce.ss destroyList
error at: conchip/mapreduce.ss main
error at: conchip/mapreduce.ss mapper_helper
error at: conchip/mapreduce.ss mapper
error at: conchip/mapreduce.ss reducer1
error at: conchip/mapreduce.ss reducer2
error at: conchip/multi-join2.ss main
error at: conchip/multi-join2.ss thread1
error at: conchip/multi-join2.ss thread2
error at: conchip/latch-exp2.ss main
error at: conchip/latch-exp2.ss thread1
error at: conchip/deadpool.ss destroyDeadPool
error at: conchip/deadpool.ss forkHelper
error at: conchip/deadpool.ss forkThreads
error at: conchip/deadpool.ss joinHelper
error at: conchip/deadpool.ss joinThreads
error at: conchip/deadpool.ss main
error at: conchip/deadpool.ss thread
.
Total verification time: 6469.91 second
	Time spent in main process: 1506.45 second
	Time spent in child processes: 4963.46 second
	Number of false contexts: 415
