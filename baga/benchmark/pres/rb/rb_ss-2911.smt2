(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun flted_12_16658 () Int)
(declare-fun bhl_16663 () Int)
(declare-fun l_16661 () Int)
(declare-fun bh () Int)
(declare-fun n () Int)
(declare-fun nl_16662 () Int)
(declare-fun tmp_primed () Int)
(declare-fun flted_12_16657 () Int)
(declare-fun bhr_16666 () Int)
(declare-fun nr_16665 () Int)
(declare-fun r_16664 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= flted_12_16658 0))
(assert (= bhl_16663 bh))
(assert (or (and (and (and (= flted_12_16658 0) (<= 2 bhl_16663)) (<= 1 nl_16662)) (> l_16661 0)) (or (and (and (and (< l_16661 1) (= nl_16662 0)) (= bhl_16663 1)) (= flted_12_16658 0)) (and (and (and (= flted_12_16658 1) (<= 1 bhl_16663)) (<= 1 nl_16662)) (> l_16661 0)))))
(assert (= bhr_16666 bh))
(assert (= flted_12_16657 0))
(assert (= n (+ (+ nr_16665 1) nl_16662)))
(assert (= tmp_primed r_16664))
(assert (or (and (and (and (= flted_12_16657 0) (<= 2 bhr_16666)) (<= 1 nr_16665)) (> r_16664 0)) (or (and (and (and (< r_16664 1) (= nr_16665 0)) (= bhr_16666 1)) (= flted_12_16657 0)) (and (and (and (= flted_12_16657 1) (<= 1 bhr_16666)) (<= 1 nr_16665)) (> r_16664 0)))))
;Negation of Consequence
(assert (not (or (= nr_16665 0) (< r_16664 1))))
(check-sat)