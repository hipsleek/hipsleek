(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun q_5426 () Int)
(declare-fun height_5421 () Int)
(declare-fun m () Int)
(declare-fun size2_5427 () Int)
(declare-fun n () Int)
(declare-fun height2_5428 () Int)
(declare-fun tmp_primed () Int)
(declare-fun size1_5424 () Int)
(declare-fun height1_5425 () Int)
(declare-fun p_5423 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (< q_5426 1) (= size2_5427 0)) (= height2_5428 0)) (and (and (<= 1 height2_5428) (<= 1 size2_5427)) (> q_5426 0))))
(assert (= height_5421 n))
(assert (= m (+ (+ size2_5427 1) size1_5424)))
(assert (<= height2_5428 (+ 1 height1_5425)))
(assert (<= height1_5425 (+ 1 height2_5428)))
(assert (exists ((max_5447 Int)) (and (= n (+ 1 max_5447)) (or (and (= max_5447 height1_5425) (>= height1_5425 height2_5428)) (and (= max_5447 height2_5428) (< height1_5425 height2_5428))))))
(assert (= tmp_primed p_5423))
(assert (or (and (and (< p_5423 1) (= size1_5424 0)) (= height1_5425 0)) (and (and (<= 1 height1_5425) (<= 1 size1_5424)) (> p_5423 0))))
;Negation of Consequence
(assert (not (or (= size1_5424 0) (or (= height1_5425 0) (< p_5423 1)))))
(check-sat)