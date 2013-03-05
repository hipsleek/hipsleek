;(set-option :auto-config false)
(set-option :pull-nested-quantifiers true)
;(set-option :macro-finder true)
;(set-option :mbqi-max-iterations 100)
(set-option :soft-timeout 400)
;(set-option :qi-max-instances 1000)

(define-sort Seqe (T) (List T))
(declare-fun length ((Seqe (Int))) Int)

;Length Axioms
(assert (forall ((l (Seqe Int))) (! (>= (length l) 0) :pattern ((length l)))))
(assert (= (length nil) 0))
(assert (forall ((l (Seqe Int))) (! (iff (= (length l) 0) (= l nil)) :pattern ((length l)))))
(assert (forall ((l (Seqe Int)) (x Int)) (! (= (length (insert x l)) (+ (length l) 1 )) :pattern ((length (insert x l))))))

(declare-fun append ((Seqe (Int)) (Seqe (Int))) (Seqe (Int)))

;Append Axioms
(assert (forall ((s (Seqe Int))) (! (and (= (append s nil) s)  (= (append nil s) s)) :pattern((append s nil) (append nil s)))))
(assert (forall ((s (Seqe Int)) (t (Seqe Int)) (x Int)) (! (= (append (insert x s) t) (insert x (append s t))) :pattern ((append (insert x s) t)))))
(assert (forall ((s0 (Seqe Int)) (s1 (Seqe Int)) (s2 (Seqe Int))) (! (= (append (append s0 s1) s2) (append s0 (append s1 s2))) :pattern ((append (append s0 s1) s2)))))
(assert (forall ((l1 (Seqe Int)) (l2 (Seqe Int))) (! (= (length (append l1 l2)) (+ (length l1) (length l2))) :pattern ((length(append l1 l2))))))

(declare-fun rev ((Seqe (Int))) (Seqe (Int)))

;Reverse axioms
(assert (= (rev nil) nil))
(assert (forall ((s (Seqe Int)) (v Int)) (! (= (rev (insert v s)) (append (rev s) (insert v nil))) :pattern((rev (insert v s))))))
(assert (forall ((s (Seqe Int))) (! (= (rev (rev s)) s) :pattern ((rev (rev s))))))
(assert (forall ((s0 (Seqe Int)) (s1 (Seqe Int))) (! (iff (= (rev s0) (rev s1)) (= s0 s1)) :pattern ((rev s0) (rev s1)))))
(assert (forall ((s (Seqe Int))) (! (= (length (rev s)) (length s)) :pattern ((length (rev s))))))
(assert (forall ((s (Seqe Int))) (! (and (= (append (rev s) nil) (rev s))  (= (append nil (rev s)) (rev s))) :pattern((append (rev s) nil) (append nil (rev s))))))
(assert (forall ((s0 (Seqe Int)) (s1 (Seqe Int))) (! (= (rev (append s0 s1)) (append (rev s1) (rev s0))) :pattern ((append (rev s1) (rev s0))))))

(declare-fun isin (Int (Seqe (Int))) Bool)

;Isin Axioms
(assert (forall ((x Int)) (not (isin x nil))))
(assert (forall ((s (Seqe Int)) (v Int) (x Int)) (! (iff (isin x (insert v s)) (or (= v x) (isin x s))) :pattern ((isin x (insert v s))))))
(assert (forall ((s0 (Seqe Int)) (s1 (Seqe Int)) (x Int)) (! (iff (isin x (append s0 s1)) (or (isin x s0) (isin x s1))) :pattern ((isin x (append s0 s1))))))
(assert (forall ((s (Seqe Int)) (x Int)) (! (iff (isin x (rev s)) (isin x s)) :pattern ((isin x (rev s))))))

(declare-fun isnotin (Int (Seqe (Int))) Bool)

;Isnotin Axioms
(assert (forall ((x Int)) (isnotin x nil)))
(assert (forall ((s (Seqe Int)) (v Int) (x Int)) (! (iff (isnotin x (insert v s)) (and (not (= v x)) (isnotin x s))) :pattern ((isnotin x (insert v s))))))
(assert (forall ((s0 (Seqe Int)) (s1 (Seqe Int)) (x Int)) (! (iff (isnotin x (append s0 s1)) (and (isnotin x s0) (isnotin x s1))) :pattern ((isnotin x (append s0 s1))))))
(assert (forall ((s (Seqe Int)) (x Int)) (! (iff (isnotin x (rev s)) (isnotin x s)) :pattern ((isnotin x (rev s))))))

(declare-fun alln ((Int) (Seqe (Int))) Bool)

;Alln axioms
(assert (forall ((n Int)) (not (alln n nil))))
(assert (forall ((s (Seqe Int)) (v Int) (n Int)) (! (iff (alln n (insert v s)) (and (= v n) (alln n s))) :pattern((alln n (insert v s))))))
(assert (forall ((s (Seqe Int)) (n Int)) (! (iff (alln n (rev s)) (alln n s)) :pattern ((alln n (rev s))))))
(assert (forall ((s0 (Seqe Int)) (s1 (Seqe Int)) (n Int)) (! (iff (alln n (append s0 s1)) (and (alln n s0) (alln n s1))) :pattern ((alln n (append s0 s1))))))
(assert (forall ((n Int) (s (Seqe Int))) (! (iff (alln n s) (forall ((x Int)) (and (iff (isin x s) (= x n)) (iff (isnotin x s) (not (= x n)))))) :pattern((alln n s)))))

(declare-fun perm ((Seqe (Int)) (Seqe (Int))) Bool)

;Perm axioms
