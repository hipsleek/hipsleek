; IMPLICATION THAT FAIL TO PROVE IN INSERTION SORT
; update_array(,a_418,(- n 1),t,b) & sorted(,a,0,n - 1) & 
;0<n & (- n 1)+1=n & (a[n])<(a[(- n 1)]) & 
; (a[n])<(a[(- n 1)]) & t=a[n] & (- n 1)+1=n & 
;update_array(,a,n,a[(- n 1)],a_418) & (- n 1)+1=n & 
;(- n 1)+1=n & sorted(,c,0,(- n 1)) & 
;idexc(,b,c,0,(- n 1)) & 
;(c[(- n 1)]=b[(- n 1)] | 
;c[(- n 1)]=b[(- n 1) - 1]) |-  sorted(,c,0,n)

(set-logic AUFNIA)

(declare-fun n () Int)
(declare-fun t () Int)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun sorted ((Array Int Int) Int Int) Bool)
(declare-fun idexc ((Array Int Int) (Array Int Int) Int Int) Bool)

(assert (forall (a (Array Int Int)) (i Int) (j Int)
                (= (sorted a i j)
                   (forall (k Int) (implies (and (<= i k) (< k j))
                                            (<= (select a k) (select a (+ k 1))))))))

(assert (forall (a (Array Int Int)) (b (Array Int Int)) (i Int) (j Int)
                (= (idexc a b i j)
                   (forall (k Int) (implies (or (< k i) (> k j))
                                            (= (select a k) (select b k)))))))

;(assert (< 1 n)) 
(assert (= n 1))
(assert (= t (select a n))) 
(assert (= b (store (store a n (select a (- n 1))) (- n 1) t)))
;(assert (sorted a 0 (- n 1)))
(assert (< (select a n) (select a (- n 1)))) 
;(assert (sorted c 0 (- n 1))) 
;(assert (idexc b c 0 (- n 1))) 
;(assert (or (= (select c (- n 1)) (select b (- n 1)))
;			(= (select c (- n 1)) (select b (- (- n 1) 1)))))
;(assert (not (sorted c 0 n)))

(check-sat)
