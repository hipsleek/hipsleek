(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun Anon_16672 () Int)
(declare-fun l_16670 () Int)
(declare-fun bh () Int)
(declare-fun bhl_16673 () Int)
(declare-fun n () Int)
(declare-fun nl_16671 () Int)
(declare-fun tmp_primed () Int)
(declare-fun Anon_16676 () Int)
(declare-fun bhr_16677 () Int)
(declare-fun nr_16675 () Int)
(declare-fun r_16674 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (and (= Anon_16672 0) (<= 2 bhl_16673)) (<= 1 nl_16671)) (> l_16670 0)) (or (and (and (and (< l_16670 1) (= nl_16671 0)) (= bhl_16673 1)) (= Anon_16672 0)) (and (and (and (= Anon_16672 1) (<= 1 bhl_16673)) (<= 1 nl_16671)) (> l_16670 0)))))
(assert (= bh (+ bhl_16673 1)))
(assert (= bhl_16673 bhr_16677))
(assert (= n (+ (+ nr_16675 1) nl_16671)))
(assert (= tmp_primed r_16674))
(assert (or (and (and (and (= Anon_16676 0) (<= 2 bhr_16677)) (<= 1 nr_16675)) (> r_16674 0)) (or (and (and (and (< r_16674 1) (= nr_16675 0)) (= bhr_16677 1)) (= Anon_16676 0)) (and (and (and (= Anon_16676 1) (<= 1 bhr_16677)) (<= 1 nr_16675)) (> r_16674 0)))))
;Negation of Consequence
(assert (not (or (= nr_16675 0) (< r_16674 1))))
(check-sat)