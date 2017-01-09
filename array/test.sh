EX="./test_ex.sh ../hip"
mkdir -p ref/draft/
mkdir -p result/draft/
mkdir -p ref/harder_array/
mkdir -p result/harder_array/
mkdir -p ref/test/
mkdir -p result/test/
$EX draft/arr_init.ss
$EX draft/arr_set.ss
$EX draft/ex11a0-infer-pre-post-arr-get.ss
$EX draft/ex11a1-infer-pre-post-var.ss
$EX draft/ex11a2-infer-pre-post-arr-get.ss
$EX draft/ex11a-infer-pre-post-arr-get.ss
$EX draft/ex11b-infer-arr-get.ss
$EX draft/ex11b-wrong-infer-arr-get.ss
$EX draft/ex11c-infer-whole-arr-get.ss
$EX draft/ex11d5-infer-arr-no-arrvar.ss
$EX draft/ex11d6-infer-arr-no-expl-updatearr.ss
$EX draft/ex11d8-infer-var.ss
$EX draft/ex11d9-infer-var-pre.ss
$EX draft/ex11d-infer-whole-arr-set.ss
$EX draft/ex11d.ss
$EX draft/ex11e1-infer-whole-arr-with-pre-set.ss
$EX draft/ex11e-infer-whole-arr-with-pre-set.ss
$EX draft/ex11-infer-arr-get.ss
$EX draft/ex12a-infer-tail-rec-2-vars.ss
$EX draft/ex12b-infer-tail-rec-2-elems.ss
$EX draft/ex12-infer-tail-rec-2-elems.ss
$EX draft/ex13a-upd-one-elem.ss
$EX draft/ex13b-upd-one-elem.ss
$EX draft/ex13c-upd-one-elem.ss
$EX draft/ex23a1-tailrec-array-loop.ss
$EX draft/ex23a2-tailrec-var-loop.ss
$EX draft/ex23a-array-loop.ss
$EX draft/ex23-array-loop.ss
$EX draft/ex24a-harder-var-loop.ss
$EX draft/ex24-harder-array-loop.ss
$EX draft/s_arr.ss
$EX harder_array/ex1-array-recursive.ss
$EX harder_array/ex2a-array-initialize.ss
$EX harder_array/ex2-array-initialize.ss
$EX harder_array/ex3a-two-array.ss
$EX harder_array/ex3.ss
$EX harder_array/ex4.ss
$EX harder_array/ex5-function.ss
$EX test/ex11c-infer-whole-arr-get.ss
$EX test/ex11d5-infer-arr-no-arrvar.ss
$EX test/ex11d8.infer-var.ss
$EX test/ex11d9-infer-var-pre.ss
$EX test/ex11d-infer-whole-arr-set.ss
$EX test/ex11d.ss
$EX test/ex11e-infer-whole-array-with-pre-set.ss
$EX test/ex11f-infer-var-with-pre-set.ss
$EX test/ex1-array-recursive.ss
$EX test/ex1b-array-recursive.ss
