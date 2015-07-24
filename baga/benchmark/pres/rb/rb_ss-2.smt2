(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun cl () Int)
(declare-fun n () Int)
(declare-fun bh () Int)
(declare-fun self () Int)
(declare-fun Anon_15 () Int)
(declare-fun bhl () Int)
(declare-fun nl () Int)
(declare-fun l () Int)
(declare-fun Anon_16 () Int)
(declare-fun bhr () Int)
(declare-fun nr () Int)
(declare-fun r () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= cl 0))
(assert (= n (+ (+ nr 1) nl)))
(assert (= bhl bhr))
(assert (= bh (+ bhl 1)))
(assert (= self 1))
(assert (or (and (and (and (= Anon_15 0) (<= 2 bhl)) (<= 1 nl)) (> l 0)) (or (and (and (and (< l 1) (= nl 0)) (= bhl 1)) (= Anon_15 0)) (and (and (and (= Anon_15 1) (<= 1 bhl)) (<= 1 nl)) (> l 0)))))
(assert (or (and (and (and (= Anon_16 0) (<= 2 bhr)) (<= 1 nr)) (> r 0)) (or (and (and (and (< r 1) (= nr 0)) (= bhr 1)) (= Anon_16 0)) (and (and (and (= Anon_16 1) (<= 1 bhr)) (<= 1 nr)) (> r 0)))))
;Negation of Consequence
(assert (not false))
(check-sat)