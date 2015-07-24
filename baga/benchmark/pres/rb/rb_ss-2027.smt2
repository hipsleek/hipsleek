(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun bh () Int)
(declare-fun l_13718 () Int)
(declare-fun Anon_13641 () Int)
(declare-fun l_13639 () Int)
(declare-fun bhl_13642 () Int)
(declare-fun n () Int)
(declare-fun nl_13640 () Int)
(declare-fun r_13721 () Int)
(declare-fun Anon_13645 () Int)
(declare-fun bhr_13646 () Int)
(declare-fun nr_13644 () Int)
(declare-fun r_13643 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= bh (+ bhl_13642 1)))
(assert (= l_13718 l_13639))
(assert (or (and (and (and (= Anon_13641 0) (<= 2 bhl_13642)) (<= 1 nl_13640)) (> l_13639 0)) (or (and (and (and (< l_13639 1) (= nl_13640 0)) (= bhl_13642 1)) (= Anon_13641 0)) (and (and (and (= Anon_13641 1) (<= 1 bhl_13642)) (<= 1 nl_13640)) (> l_13639 0)))))
(assert (= bhl_13642 bhr_13646))
(assert (= n (+ (+ nr_13644 1) nl_13640)))
(assert (= r_13721 r_13643))
(assert (or (and (and (and (= Anon_13645 0) (<= 2 bhr_13646)) (<= 1 nr_13644)) (> r_13643 0)) (or (and (and (and (< r_13643 1) (= nr_13644 0)) (= bhr_13646 1)) (= Anon_13645 0)) (and (and (and (= Anon_13645 1) (<= 1 bhr_13646)) (<= 1 nr_13644)) (> r_13643 0)))))
;Negation of Consequence
(assert (not (or (= nr_13644 0) (< r_13643 1))))
(check-sat)