(define-sort Seq (T) (List T))

(declare-fun length ((Seq (Int))) Int)
;Length Axioms
(assert (forall ((l (Seq Int))) (! (>= (length l) 0) :pattern ((length l)))))

(assert (forall ((l (Seq Int)) (x Int)) 
(! (= (length (insert x l)) (+ (length l) 1 )) :pattern ((length (insert x l))))))

(assert (forall ((x Int)) 
(! (= (length (insert x nil)) 1) :pattern ((length (insert x nil))))))

(assert (= (length nil) 0))

(assert (forall ((l (Seq Int))) 
(! (=> (= (length l) 0) (= l nil)) :pattern ((length l)))))

(declare-fun append ((Seq (Int)) (Seq (Int))) (Seq (Int)))
;Append Axioms
(assert (forall ((l1 (Seq Int)) (l2 (Seq Int))) 
(! (= (length (append l1 l2)) (+ (length l1) (length l2))) :pattern ((length(append l1 l2))))))

(declare-fun index ((Seq (Int)) Int) Int)
;Index Axioms
(assert (forall ((s (Seq Int)) (i Int) (v Int)) 
(! (and (=> (= i (length s)) (= (index (insert v s) i) v)) (=> (not (= i (length s))) (= (index (insert v s) i) (index s i)))) 
:pattern ((index (insert v s) i)))))

(assert (forall ((s0 (Seq Int)) (s1 (Seq Int)) (n Int)) 
(! (and (=> (< n (length s0))(= (index (append s0 s1) n) (index s0 n))) (=> (<= (length s0) n) (= (index(append s0 s1) n) (- (index s1 n) (length s0))))) 
:pattern ((index (append s0 s1) n)))))

(declare-fun isin ((Seq (Int)) Int) Bool)
;isin Axioms
(assert (forall ((s (Seq Int)) (x Int))
(! (iff (isin s x) (exists ((i Int)) (! (and (<= 0 i) (and (< i (length s)) (= (index s i) x))) :pattern ((index s i))))) :pattern ((isin s x)))))

(assert (forall ((s0 (Seq Int)) (s1 (Seq Int)) (x Int)) 
(! (iff (isin (append s0 s1) x) (or (isin s0 x) (isin s1 x))) :pattern ((isin (append s0 s1) x)))))

(assert (forall ((s (Seq Int)) (v Int) (x Int))
(! (iff (isin (insert v s) x) (or (= v x) (isin s x))) :pattern ((isin (insert v s) x)))))

(declare-fun isnotin ((Seq (Int)) Int) Bool)
;isnotin Axioms
(assert (forall ((s (Seq Int)) (x Int))
(! (iff (isnotin s x) (forall ((i Int)) (! (and (<= 0 i) (and (< i (length s)) (not (= (index s i) x)))) :pattern ((index s i))))) :pattern ((isnotin s x)))))

(assert (forall ((s0 (Seq Int)) (s1 (Seq Int)) (x Int)) 
(! (iff (isnotin (append s0 s1) x) (and (isnotin s0 x) (isnotin s1 x))) :pattern ((isnotin (append s0 s1) x)))))

(assert (forall ((s (Seq Int)) (v Int) (x Int))
(! (iff (isnotin (insert v s) x) (and (not (= v x)) (isnotin s x))) :pattern ((isnotin (insert v s) x)))))

(declare-fun rev ((Seq (Int))) (Seq (Int)))
;reverse axioms
(assert (forall ((s (Seq Int)))
(! (= (length (rev s)) (length s)) :pattern ((length (rev s))))))

(assert (forall ((s (Seq Int)) (i Int))
(! (= (index (rev s) i) (index s (- (length s) i))) :pattern ((index (rev s) i)))))

(declare-fun eq ((Seq (Int)) (Seq (Int))) Bool)
;eq axioms
(assert (forall ((s0 (Seq Int)) (s1 (Seq Int)))
(! (iff (eq s0 s1) (and (= (length s0) (length s1)) (forall ((j Int)) (! (=> (and (<= 0 j) (< j (length s0))) (= (index s0 j) (index s1 j))) 
:pattern ((index s0 j) (index s1 j)))))) :pattern((eq s0 s1)))))

(assert (forall ((s0 (Seq Int)) (s1 (Seq Int)))
(! (=> (eq s0 s1) (= s0 s1)) :pattern ((eq s0 s1)))))

(assert (forall ((s0 (Seq Int)) (s1 (Seq Int)))
(! (iff (eq (rev s0) (rev s1)) (eq s0 s1)) :pattern ((eq (rev s0) (rev s1))))))

(assert (forall ((s (Seq Int)))
(! (eq (rev (rev s)) s) :pattern ((rev (rev s))))))

(assert (forall ((s0 (Seq Int)) (s1 (Seq Int)) (s2 (Seq Int)))
(! (eq (append (append s0 s1) s2) (append s0 (append s1 s2))) :pattern ((append (append s0 s1) s2) (append s0 (append s1 s2))))))

(declare-fun alln ((Int) (Seq (Int))) Bool)
;alln axioms
(assert (forall ((x Int) (s (Seq Int)))
(! (=> (alln x s)  (forall ((i Int)) (! (= (index s i) x) :pattern ((index s i))))) :pattern ((alln x s)))))