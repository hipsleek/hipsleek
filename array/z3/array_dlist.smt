(declare-datatypes (T) ((Lst nil (cons (prev Lst) (val T) (next Lst)))))
(declare-const l1 (Lst Int))
(declare-const l2 (Lst Int))
(declare-const l3 (Lst Int))

(assert (= (val l1) 10))
(assert (= (val l2) 20))
(assert (= (val l3) 30))

(assert (= (prev l2) l1))
(assert (= (next l2) l3))

(declare-const a1 (Array Int (Lst Int)))
(declare-const a2 (Array Int (Lst Int)))
(assert (= (store a1 0 l2) a2))

(assert (not (= (val (prev (select a2 0))) 10)))

(check-sat)