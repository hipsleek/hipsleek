(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun Anon_40 () Int)
(declare-fun cm () Int)
(declare-fun c () Int)
(declare-fun cn () Int)
(declare-fun r () Int)
(declare-fun Anon_36 () Int)
(declare-fun dm () Int)
(declare-fun dn () Int)
(declare-fun d () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (and (< c 1) (= cm 0)) (= cn 0)) (= Anon_40 1)) (and (and (and (and (and (<= 0 Anon_40) (<= (+ (- 0 cn) 2) Anon_40)) (<= Anon_40 cn)) (<= Anon_40 2)) (<= 1 cm)) (> c 0))))
(assert (<= dn (+ cn 1)))
(assert (<= cn (+ dn 1)))
(assert (= r d))
(assert (or (and (and (and (< d 1) (= dm 0)) (= dn 0)) (= Anon_36 1)) (and (and (and (and (and (<= 0 Anon_36) (<= (+ (- 0 dn) 2) Anon_36)) (<= Anon_36 dn)) (<= Anon_36 2)) (<= 1 dm)) (> d 0))))
;Negation of Consequence
(assert (not (or (= dm 0) (or (= dn 0) (< d 1)))))
(check-sat)