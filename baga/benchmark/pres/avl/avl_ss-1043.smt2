(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun q_6999 () Int)
(declare-fun height_6994 () Int)
(declare-fun v_node_468_1377_primed () Int)
(declare-fun h1 () Int)
(declare-fun height2_7001 () Int)
(declare-fun s1 () Int)
(declare-fun size2_7000 () Int)
(declare-fun size1_6997 () Int)
(declare-fun height1_6998 () Int)
(declare-fun p_6996 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (< q_6999 1) (= size2_7000 0)) (= height2_7001 0)) (and (and (<= 1 height2_7001) (<= 1 size2_7000)) (> q_6999 0))))
(assert (= height_6994 h1))
(assert (= v_node_468_1377_primed p_6996))
(assert (exists ((max_7031 Int)) (and (= h1 (+ 1 max_7031)) (or (and (= max_7031 height1_6998) (>= height1_6998 height2_7001)) (and (= max_7031 height2_7001) (< height1_6998 height2_7001))))))
(assert (<= height1_6998 (+ 1 height2_7001)))
(assert (<= height2_7001 (+ 1 height1_6998)))
(assert (= s1 (+ (+ size2_7000 1) size1_6997)))
(assert (or (and (and (< p_6996 1) (= size1_6997 0)) (= height1_6998 0)) (and (and (<= 1 height1_6998) (<= 1 size1_6997)) (> p_6996 0))))
;Negation of Consequence
(assert (not (or (= size1_6997 0) (or (= height1_6998 0) (< p_6996 1)))))
(check-sat)