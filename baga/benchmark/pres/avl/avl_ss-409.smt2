(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun p_4547 () Int)
(declare-fun height_4545 () Int)
(declare-fun m () Int)
(declare-fun size1_4548 () Int)
(declare-fun n () Int)
(declare-fun height1_4549 () Int)
(declare-fun tmp_primed () Int)
(declare-fun size2_4551 () Int)
(declare-fun height2_4552 () Int)
(declare-fun q_4550 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (< p_4547 1) (= size1_4548 0)) (= height1_4549 0)) (and (and (<= 1 height1_4549) (<= 1 size1_4548)) (> p_4547 0))))
(assert (= height_4545 n))
(assert (= m (+ (+ size2_4551 1) size1_4548)))
(assert (<= height2_4552 (+ 1 height1_4549)))
(assert (<= height1_4549 (+ 1 height2_4552)))
(assert (exists ((max_4923 Int)) (and (= n (+ 1 max_4923)) (or (and (= max_4923 height1_4549) (>= height1_4549 height2_4552)) (and (= max_4923 height2_4552) (< height1_4549 height2_4552))))))
(assert (= tmp_primed q_4550))
(assert (or (and (and (< q_4550 1) (= size2_4551 0)) (= height2_4552 0)) (and (and (<= 1 height2_4552) (<= 1 size2_4551)) (> q_4550 0))))
;Negation of Consequence
(assert (not (or (= size2_4551 0) (or (= height2_4552 0) (< q_4550 1)))))
(check-sat)