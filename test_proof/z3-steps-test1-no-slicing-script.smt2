(push)
(declare-const x Int)
(declare-const y Int)
(declare-const x1 Int)
(declare-const y1 Int)
(declare-const res Bool)
 (push);  
   (assert (< 2 x))
   (assert (<= 0 y))
   (push) ; 
     (assert (= x1 (+ 1 x))) 
     (assert (= y1 (+ 1 y)))
     (push); 
       (assert (< 3 x1))
       (assert res)
       (check-sat)
     (pop);
     (push); 
       (assert (<= x1 3))
       (assert (not res))
       (check-sat)
     (pop); 
     (push); 
       (declare-const b_191 Bool)
       (assert (< 3 x1))
       (assert b_191)
       (assert (< 3 x1))
       (push) ; pu5
         (assert b_191)
         (check-sat)
       (pop) ; 
       (push) ; 
         (assert (not b_191)) 
         (check-sat)
       (pop) ; 
     (pop) ; 
   (pop) ; 
   (push) ; 
     (declare-const b_547 Bool)
     (assert (and (and (and (and (and (< 3 (+ 1 x)) b_547) (< 3 (+ 1 x))) b_547) (= (+ x1 (* 1 1)) (+ 1 x)))  (= y1 (+ (+ 1 1) y))))
     (push)
       (assert (not (= x1 x)))
       (check-sat)
     (pop)
     (push)
       (assert (not (< 1 y1)))
       (check-sat)
     (pop)
   (pop) ; 
 (pop) ; 
(pop)  
