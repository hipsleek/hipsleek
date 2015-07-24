(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun Anon_38 () Int)
(declare-fun cm () Int)
(declare-fun c () Int)
(declare-fun cn () Int)
(declare-fun r () Int)
(declare-fun Anon_34 () Int)
(declare-fun dm () Int)
(declare-fun dn () Int)
(declare-fun d () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (and (< c 1) (= cm 0)) (= cn 0)) (= Anon_38 1)) (and (and (and (and (and (<= 0 Anon_38) (<= (+ (- 0 cn) 2) Anon_38)) (<= Anon_38 cn)) (<= Anon_38 2)) (<= 1 cm)) (> c 0))))
(assert (<= dn (+ cn 1)))
(assert (<= cn (+ dn 1)))
(assert (= r d))
(assert (or (and (and (and (< d 1) (= dm 0)) (= dn 0)) (= Anon_34 1)) (and (and (and (and (and (<= 0 Anon_34) (<= (+ (- 0 dn) 2) Anon_34)) (<= Anon_34 dn)) (<= Anon_34 2)) (<= 1 dm)) (> d 0))))
;Negation of Consequence
(assert (not (or (= dm 0) (or (= dn 0) (< d 1)))))
(check-sat)