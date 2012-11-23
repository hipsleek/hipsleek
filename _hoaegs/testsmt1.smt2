(set-logic AUFNIA)

(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun c () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun k () Int)
(declare-fun n () Int)
(declare-fun t () Int)
(declare-fun sorted ((Array Int Int) Int Int) Bool)
(declare-fun upperbnd ((Array Int Int) Int Int Int) Bool)
(declare-fun ubpreserving ((Array Int Int) (Array Int Int) Int Int) Bool)
(declare-fun identicalout ((Array Int Int) (Array Int Int) Int Int) Bool)

(assert (forall (a (Array Int Int)) (i Int) (j Int)
                (= (sorted a i j)
                   (forall (k Int) (implies (and (<= i k) (< k j))
                                            (<= (select a k) (select a (+ k 1))))))))

(assert (forall (a (Array Int Int)) (i Int) (j Int) (u Int)
                (= (upperbnd a i j u)
                   (forall (k Int) (implies (and (<= i k) (<= k j))
                                            (<= (select a k) u))))))

(assert (forall (a (Array Int Int)) (b (Array Int Int)) (i Int) (j Int)
                (= (ubpreserving a b i j)
                   (forall (u Int) (implies (upperbnd a i j u)
                                            (upperbnd b i j u))))))

(assert (forall (a (Array Int Int)) (b (Array Int Int)) (i Int) (j Int)
                (= (identicalout a b i j)
                   (forall (k Int) (implies (or (< k i) (> k j))
                                            (= (select a k) (select b k)))))))

; 0<=i & 0<=j & i<j & i<=k_37' & k_37'<=j & upperbnd(,a,i,j,a[k_37']) & 
;i<=j & temp_38'=a[k_37'] & update_array(,a,k_37',a[j],a_270) & 
;update_array(,a_270,j,temp_38',a_272) & v_int_47_273+1=j & 
;sorted(,a',i,v_int_47_273) & idexc(,a',a_272,i,v_int_47_273) & 
;upperbndprev(,a_272,a',i,v_int_47_273) |-  sorted(,a',i,j)

(assert (<= 0 i))
(assert (<= 0 j))
(assert (< i j))
(assert (<= i k))
(assert (<= k j))
(assert (upperbnd a i j (select a k)))
(assert (= t (select a k)))
(assert (= b (store (store a k (select a j)) j t)))
;(assert (upperbnd b i (- j 1) t))
(assert (not (upperbnd b i (- j 1) t)))
;(assert (sorted c i (- j 1)))
;(assert (identicalout c b i (- j 1)))
;(assert (ubpreserving b c i (- j 1)))
;(assert (not (sorted c i j)))

(check-sat)