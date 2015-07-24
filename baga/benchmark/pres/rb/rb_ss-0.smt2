(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun bh () Int)
(declare-fun n () Int)
(declare-fun cl () Int)
(declare-fun self () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (exists ((nr Int)) (and (or (and (and (and (exists ((r Int)) (> r 0)) (= 0 0)) (<= 2 bh)) (<= 1 nr)) (or (and (and (= nr 0) (= bh 1)) (= 0 0)) (and (and (and (exists ((r Int)) (> r 0)) (= 0 1)) (<= 1 bh)) (<= 1 nr)))) (exists ((nl Int)) (and (or (and (and (and (exists ((l Int)) (> l 0)) (= 0 0)) (<= 2 bh)) (<= 1 nl)) (or (and (and (= nl 0) (= bh 1)) (= 0 0)) (and (and (and (exists ((l Int)) (> l 0)) (= 0 1)) (<= 1 bh)) (<= 1 nl)))) (= n (+ (+ nr 1) nl)))))))
(assert (= cl 1))
(assert (= self 1))
;Negation of Consequence
(assert (not false))
(check-sat)