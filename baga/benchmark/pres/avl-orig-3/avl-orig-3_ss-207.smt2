(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun Anon_31 () Int)
(declare-fun am () Int)
(declare-fun a () Int)
(declare-fun an () Int)
(declare-fun ll () Int)
(declare-fun Anon_37 () Int)
(declare-fun bm () Int)
(declare-fun bn () Int)
(declare-fun b () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (and (< a 1) (= am 0)) (= an 0)) (= Anon_31 1)) (and (and (and (and (and (<= 0 Anon_31) (<= (+ (- 0 an) 2) Anon_31)) (<= Anon_31 an)) (<= Anon_31 2)) (<= 1 am)) (> a 0))))
(assert (<= an (+ bn 1)))
(assert (<= bn (+ an 1)))
(assert (= ll b))
(assert (or (and (and (and (< b 1) (= bm 0)) (= bn 0)) (= Anon_37 1)) (and (and (and (and (and (<= 0 Anon_37) (<= (+ (- 0 bn) 2) Anon_37)) (<= Anon_37 bn)) (<= Anon_37 2)) (<= 1 bm)) (> b 0))))
;Negation of Consequence
(assert (not (or (= bm 0) (or (= bn 0) (< b 1)))))
(check-sat)