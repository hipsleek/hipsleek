(set-logic QF_LIA)
;Variables declarations
(declare-fun x () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (< 3 (* 3 x)))
;Negation of Consequence
(assert (not false))
(check-sat)