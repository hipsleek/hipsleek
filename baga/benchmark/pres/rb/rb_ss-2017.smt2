(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun r_13695 () Int)
(declare-fun Anon_13645 () Int)
(declare-fun r_13643 () Int)
(declare-fun bhr_13646 () Int)
(declare-fun bh () Int)
(declare-fun n () Int)
(declare-fun nr_13644 () Int)
(declare-fun l_13691 () Int)
(declare-fun Anon_13641 () Int)
(declare-fun bhl_13642 () Int)
(declare-fun nl_13640 () Int)
(declare-fun l_13639 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= r_13695 r_13643))
(assert (or (and (and (and (= Anon_13645 0) (<= 2 bhr_13646)) (<= 1 nr_13644)) (> r_13643 0)) (or (and (and (and (< r_13643 1) (= nr_13644 0)) (= bhr_13646 1)) (= Anon_13645 0)) (and (and (and (= Anon_13645 1) (<= 1 bhr_13646)) (<= 1 nr_13644)) (> r_13643 0)))))
(assert (= bhl_13642 bhr_13646))
(assert (= bh (+ bhl_13642 1)))
(assert (= n (+ (+ nr_13644 1) nl_13640)))
(assert (= l_13691 l_13639))
(assert (or (and (and (and (= Anon_13641 0) (<= 2 bhl_13642)) (<= 1 nl_13640)) (> l_13639 0)) (or (and (and (and (< l_13639 1) (= nl_13640 0)) (= bhl_13642 1)) (= Anon_13641 0)) (and (and (and (= Anon_13641 1) (<= 1 bhl_13642)) (<= 1 nl_13640)) (> l_13639 0)))))
;Negation of Consequence
(assert (not (or (= nl_13640 0) (< l_13639 1))))
(check-sat)