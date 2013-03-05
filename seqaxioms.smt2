(set-option :auto-config false)
(set-option :pull-nested-quantifiers true)
;(set-option :macro-finder true)
;(set-option :mbqi-max-iterations 100)
(set-option :soft-timeout 400)
;(set-option :qi-max-instances 1000)

(define-sort Seq (T) (List T))
(declare-fun length ((Seq (Int))) Int)

;Length Axioms
(assert (forall ((l (Seq Int))) (! (>= (length l) 0) :pattern ((length l)))))
(assert (= (length nil) 0))
(assert (forall ((l (Seq Int))) (! (iff (= (length l) 0) (= l nil)) :pattern ((length l)))))
(assert (forall ((l (Seq Int)) (x Int)) (! (= (length (insert x l)) (+ (length l) 1 )) :pattern ((length (insert x l))))))

(declare-fun append ((Seq (Int)) (Seq (Int))) (Seq (Int)))

;Append Axioms
(assert (forall ((s (Seq Int))) (! (and (= (append s nil) s)  (= (append nil s) s)) :pattern((append s nil) (append nil s)))))
(assert (forall ((s (Seq Int)) (t (Seq Int)) (x Int)) (! (= (append (insert x s) t) (insert x (append s t))) :pattern ((append (insert x s) t)))))
(assert (forall ((s0 (Seq Int)) (s1 (Seq Int)) (s2 (Seq Int))) (! (= (append (append s0 s1) s2) (append s0 (append s1 s2))) :pattern ((append (append s0 s1) s2)))))
(assert (forall ((l1 (Seq Int)) (l2 (Seq Int))) (! (= (length (append l1 l2)) (+ (length l1) (length l2))) :pattern ((length(append l1 l2))))))

(declare-fun rev ((Seq (Int))) (Seq (Int)))

;Reverse axioms
(assert (= (rev nil) nil))
(assert (forall ((s (Seq Int)) (v Int)) (! (= (rev (insert v s)) (append (rev s) (insert v nil))) :pattern((rev (insert v s))))))
(assert (forall ((s (Seq Int))) (! (= (rev (rev s)) s) :pattern ((rev (rev s))))))
(assert (forall ((s0 (Seq Int)) (s1 (Seq Int))) (! (iff (= (rev s0) (rev s1)) (= s0 s1)) :pattern ((rev s0) (rev s1)))))
(assert (forall ((s (Seq Int))) (! (= (length (rev s)) (length s)) :pattern ((length (rev s))))))
(assert (forall ((s (Seq Int))) (! (and (= (append (rev s) nil) (rev s))  (= (append nil (rev s)) (rev s))) :pattern((append (rev s) nil) (append nil (rev s))))))
(assert (forall ((s0 (Seq Int)) (s1 (Seq Int))) (! (= (rev (append s0 s1)) (append (rev s1) (rev s0))) :pattern ((append (rev s1) (rev s0))))))

(declare-fun isin (Int (Seq (Int))) Bool)

;Isin Axioms
(assert (forall ((x Int)) (not (isin x nil))))
(assert (forall ((s (Seq Int)) (v Int) (x Int)) (! (iff (isin x (insert v s)) (or (= v x) (isin x s))) :pattern ((isin x (insert v s))))))
(assert (forall ((s0 (Seq Int)) (s1 (Seq Int)) (x Int)) (! (iff (isin x (append s0 s1)) (or (isin x s0) (isin x s1))) :pattern ((isin x (append s0 s1))))))
(assert (forall ((s (Seq Int)) (x Int)) (! (iff (isin x (rev s)) (isin x s)) :pattern ((isin x (rev s))))))

(declare-fun isnotin (Int (Seq (Int))) Bool)

;Isnotin Axioms
(assert (forall ((x Int)) (isnotin x nil)))
(assert (forall ((s (Seq Int)) (v Int) (x Int)) (! (iff (isnotin x (insert v s)) (and (not (= v x)) (isnotin x s))) :pattern ((isnotin x (insert v s))))))
(assert (forall ((s0 (Seq Int)) (s1 (Seq Int)) (x Int)) (! (iff (isnotin x (append s0 s1)) (and (isnotin x s0) (isnotin x s1))) :pattern ((isnotin x (append s0 s1))))))
(assert (forall ((s (Seq Int)) (x Int)) (! (iff (isnotin x (rev s)) (isnotin x s)) :pattern ((isnotin x (rev s))))))

(declare-fun alln ((Int) (Seq (Int))) Bool)

;Alln axioms
(assert (forall ((n Int)) (not (alln n nil))))
(assert (forall ((s (Seq Int)) (v Int) (n Int)) (! (iff (alln n (insert v s)) (and (= v n) (alln n s))) :pattern((alln n (insert v s))))))
(assert (forall ((s (Seq Int)) (n Int)) (! (iff (alln n (rev s)) (alln n s)) :pattern ((alln n (rev s))))))
(assert (forall ((s0 (Seq Int)) (s1 (Seq Int)) (n Int)) (! (iff (alln n (append s0 s1)) (and (alln n s0) (alln n s1))) :pattern ((alln n (append s0 s1))))))
(assert (forall ((n Int) (s (Seq Int))) (! (iff (alln n s) (forall ((x Int)) (and (iff (isin x s) (= x n)) (iff (isnotin x s) (not (= x n)))))) :pattern((alln n s)))))

(declare-fun perm ((Seq (Int)) (Seq (Int))) Bool)

;Perm axioms
