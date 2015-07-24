(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun n () Int)
(declare-fun bh () Int)
(declare-fun cl () Int)
(declare-fun self () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (exists ((bhr Int)) (and (exists ((Anon_16 Int)) (exists ((nr Int)) (and (or (and (and (and (exists ((r Int)) (> r 0)) (= Anon_16 0)) (<= 2 bhr)) (<= 1 nr)) (or (and (and (= nr 0) (= bhr 1)) (= Anon_16 0)) (and (and (and (exists ((r Int)) (> r 0)) (= Anon_16 1)) (<= 1 bhr)) (<= 1 nr)))) (exists ((Anon_15 Int)) (exists ((nl Int)) (and (or (and (and (and (exists ((l Int)) (> l 0)) (= Anon_15 0)) (<= 2 bhr)) (<= 1 nl)) (or (and (and (= nl 0) (= bhr 1)) (= Anon_15 0)) (and (and (and (exists ((l Int)) (> l 0)) (= Anon_15 1)) (<= 1 bhr)) (<= 1 nl)))) (= n (+ (+ nr 1) nl)))))))) (= bh (+ bhr 1)))))
(assert (= cl 0))
(assert (= self 1))
;Negation of Consequence
(assert (not false))
(check-sat)