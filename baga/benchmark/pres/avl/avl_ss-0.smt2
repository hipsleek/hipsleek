(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun size () Int)
(declare-fun height () Int)
(declare-fun self () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (exists ((height2 Int)) (exists ((size2 Int)) (and (or (and (= size2 0) (= height2 0)) (and (and (exists ((q Int)) (> q 0)) (<= 1 height2)) (<= 1 size2))) (exists ((height1 Int)) (and (and (and (exists ((size1 Int)) (and (or (and (= size1 0) (= height1 0)) (and (and (exists ((p Int)) (> p 0)) (<= 1 height1)) (<= 1 size1))) (= size (+ (+ size2 1) size1)))) (<= height2 (+ 1 height1))) (<= height1 (+ 1 height2))) (exists ((max_33 Int)) (and (= height (+ 1 max_33)) (or (and (= max_33 height1) (>= height1 height2)) (and (= max_33 height2) (< height1 height2)))))))))))
(assert (= self 1))
;Negation of Consequence
(assert (not false))
(check-sat)