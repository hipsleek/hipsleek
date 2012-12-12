(set-logic AUFNIA)

(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)

(declare-fun permutation ((Array Int Int) Int Int (Array Int Int) Int Int) Bool)

(assert (forall (a (Array Int Int)) (b (Array Int Int)) (i Int) (u Int) (j Int) (v Int) (a (Array Int Int)) (b (Array Int Int)) (u Int) (v Int)(implies (and (forall (?k Int) (or (= ?k i) (or (= ?k j) (= (select a ?k) (select b ?k))))) (and (= (select a i) (select b j)) (and (= (select a j) (select b i)) (and (and (<= u i) (<= i v)) (and (<= u j) (<= j v))))))
(permutation a u v b u v))))

(assert (forall (i Int) (l Int) (a (Array Int Int)) (j Int) (b (Array Int Int)) (h Int) (a (Array Int Int)) (i Int) (j Int) (b (Array Int Int)) (l Int) (h Int)(implies (and (permutation a i j b l h) (= (select a (+ j 1)) (select b (+ h 1))))
(permutation a i (+ j 1) b l (+ h 1)))))

(assert (forall (a (Array Int Int)) (i Int) (j Int) (b (Array Int Int)) (l Int) (h Int) (c (Array Int Int)) (u Int) (v Int) (a (Array Int Int)) (i Int) (j Int) (c (Array Int Int)) (u Int) (v Int)(implies (and (permutation a i j b l h) (permutation b l h c u v))
(permutation a i j c u v))))

(assert (forall (a (Array Int Int)) (i Int) (j Int) (b (Array Int Int)) (l Int) (h Int) (b (Array Int Int)) (l Int) (h Int) (a (Array Int Int)) (i Int) (j Int)(implies (permutation a i j b l h)
(permutation b l h a i j))))

(assert (forall (a (Array Int Int)) (i Int) (j Int)(implies true
(permutation a i j a i j))))


(assert (= b (store a i (select a j))))
(assert (= c (store b j (select a i))))
(assert (= (select c i) (select a j)))
(assert (= (select c j) (select a i)))
(assert (forall (k Int) (implies (and (distinct k i) (distinct k j)) (= (select c k) (select a k)))))
(assert (not (permutation c i j a i j)))

(check-sat)
