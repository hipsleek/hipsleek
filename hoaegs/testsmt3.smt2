; 0<=i & 0<=j & 124i<j & 135i<=k_37' & 136k_37'<=j & 
;137upperbnd(,a,i,j,a[k_37']) & 138i<=j & 143temp_38'=a[k_37'] & 
;149update_array(,a,k_37',a[j],a_295) & 
;152update_array(,a_295,j,temp_38',a_297) & upperbnd(,a_297,i,j -
;1,temp_38') & 157v_int_56_298+1=j & 160sorted(,a',i,v_int_56_298) & 
;161idexc(,a',a_297,i,v_int_56_298) & 
;162upperbndprev(,a_297,a',i,v_int_56_298) & 
;163arrayperm(,a',i,v_int_56_298,a_297,i,v_int_56_298) 
;|-  arrayperm(,a',i,j,a,i,j)

(set-logic AUFNIA)

(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))

(declare-fun freq ((Array Int Int) Int Int Int Int) Bool)

(declare-fun arrayperm ((Array Int Int) Int Int (Array Int Int) Int Int) Bool)

(assert (forall (a (Array Int Int)) (i Int) (j Int) (x Int) (s Int)
		(= 	(freq a i j x s)
			(or (and (> i j) (= s 0))
			(or	(and (= (select a i) x) (freq a (+ i 1) j x (- s 1)))
			(and (distinct (select a i) x) (freq a (+ i 1) j x s)))))))

(assert (forall (a (Array Int Int)) (i Int) (j Int) (x Int) (s Int)
		(= 	(freq a i j x s)
			(or (and (> i j) (= s 0))
			(or	(and (= (select a j) x) (freq a i (- j 1) x (- s 1)))
			(and (distinct (select a j) x) (freq a i (- j 1) x s)))))))

(assert (forall (a (Array Int Int)) (i Int) (j Int)
				(b (Array Int Int)) (m Int) (n Int)
		(= 	(arrayperm a i j b m n)
			(forall (x Int) (s Int) (t Int)
					(implies (and (freq a i j x s) (freq b m n x t)) (= s t))))))

(assert (forall (a (Array Int Int)) (i Int) (j Int)
				(b (Array Int Int)) (m Int) (n Int)
		(= 	(arrayperm a i j b m n)
			(forall (k Int) (s Int)
					(and (implies (and (<= i k) (and (<= k j) (freq a i j (select a k) s))) (freq b m n (select a k) s)) (implies (and (<= m k) (and (<= k n) (freq b m n (select b k) s))) (freq a i j (select b k) s)))))))

(assert (= (select a 0) 0))
(assert (= (select a 1) 0))
(assert (= (select a 2) 0))
(assert (not (freq a 0 2 0 3)))

;(assert (<= 0 i))
;(assert (<= 0 j))
;(assert (<= i j))
;(assert (= (select c j) (select b j)))
;(assert (arrayperm c i (- j 1) b i (- j 1)))
;(assert (not (arrayperm c i j b i j)))

(check-sat)
