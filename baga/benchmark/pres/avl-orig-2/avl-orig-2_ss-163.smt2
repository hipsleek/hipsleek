(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun Anon_20 () Int)
(declare-fun dm () Int)
(declare-fun d () Int)
(declare-fun dn () Int)
(declare-fun rr () Int)
(declare-fun Anon_27 () Int)
(declare-fun cm () Int)
(declare-fun cn () Int)
(declare-fun c () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (and (< d 1) (= dm 0)) (= dn 0)) (= Anon_20 1)) (and (and (and (and (and (<= 0 Anon_20) (<= (+ (- 0 dn) 2) Anon_20)) (<= Anon_20 dn)) (<= Anon_20 2)) (<= 1 dm)) (> d 0))))
(assert (<= dn (+ cn 1)))
(assert (<= cn (+ dn 1)))
(assert (= rr c))
(assert (or (and (and (and (< c 1) (= cm 0)) (= cn 0)) (= Anon_27 1)) (and (and (and (and (and (<= 0 Anon_27) (<= (+ (- 0 cn) 2) Anon_27)) (<= Anon_27 cn)) (<= Anon_27 2)) (<= 1 cm)) (> c 0))))
;Negation of Consequence
(assert (not (or (= cm 0) (or (= cn 0) (< c 1)))))
(check-sat)