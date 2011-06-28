; FAIL IMPLICATION FOR QUICk SORT
; 130i<=j & 141strupperbnd(,b,i,k,a[i]) & 142alleqs(,b,k+
;1,t - 1,a[i]) & 143strlowerbnd(,b,t,j,a[i]) & 
;144idexc(,b,a,i,j) & 147sorted(,c,i,k) & 
;148idexc(,c,b,i,k) & 151sorted(,d,t,j) & 
;152idexc(,d,c,t,j) |-  sorted(,d,i,j)



(set-logic AUFNIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun k () Int)
(declare-fun c () (Array Int Int))
(declare-fun t () Int)
(declare-fun d () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun alleqs ((Array Int Int) Int Int Int) Bool)
(declare-fun strlowerbnd ((Array Int Int) Int Int Int) Bool)
(declare-fun strupperbnd ((Array Int Int) Int Int Int) Bool)
(declare-fun sorted ((Array Int Int) Int Int) Bool)
(declare-fun idexc ((Array Int Int) (Array Int Int) Int Int) Bool)
(assert (forall (a (Array Int Int)) (i Int) (j Int) (s Int) (= (alleqs a i j s) (or (> i j) (forall (?k Int) (or (or (< ?k i) (> ?k j)) (= (select a ?k) s)))))))
(assert (forall (a (Array Int Int)) (i Int) (j Int) (s Int) (= (strlowerbnd a i j s) (or (> i j) (forall (?k Int) (or (or (< ?k i) (> ?k j)) (> (select a ?k) s)))))))
(assert (forall (a (Array Int Int)) (i Int) (j Int) (s Int) (= (strupperbnd a i j s) (or (> i j) (forall (?k Int) (or (or (< ?k i) (> ?k j)) (< (select a ?k) s)))))))
(assert (forall (a (Array Int Int)) (i Int) (j Int) (= (sorted a i j) (or (>= i j) (forall (?k Int) (or (or (< ?k i) (>= ?k j)) (<= (select a ?k) (select a (+ ?k 1)))))))))
(assert (forall (a (Array Int Int)) (b (Array Int Int)) (i Int) (j Int) (= (idexc a b i j) (forall (?k Int) (or (and (<= i ?k) (<= ?k j)) (= (select a ?k) (select b ?k)))))))


(assert (<= i j))
(assert (< i k))
(assert (< k t))
(assert (< t j))
(assert (strupperbnd b i k (select a i))) 
(assert (alleqs b (+ k 1) (- t 1) (select a i))) 
(assert (strlowerbnd b t j (select a i))) 
(assert (idexc b a i j)) 
(assert (sorted c i k)) 
(assert (idexc c b i k)) 
(assert (sorted d t j)) 
(assert (idexc d c t j))
(assert (not (sorted d i j)))

(check-sat)

