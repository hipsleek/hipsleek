(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

(declare-const a1 (Array Int (Pair Int Int)))

(declare-const p1 (Pair Int Int))
(assert (= (first p1) 10))
(assert (= (second p1) 10))

(declare-const a2 (Array Int (Pair Int Int)))
(assert (= (store a1 0 p1) a2))

(declare-const i Int)
(assert (= i 0))

(declare-const p2 (Pair Int Int))
(assert (= (select a2 i) p2))

(declare-const p3 (Pair Int Int))
(assert (= (first p3) 20))
(assert (= (second p3) (second p2)))

(declare-const a3 (Array Int (Pair Int Int)))
(assert (= (store a2 i p3) a3))

;(assert (not (= (first (select a3 0)) 20)))
(assert (not (= (second (select a3 0)) 10)))

(check-sat)