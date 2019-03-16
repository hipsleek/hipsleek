;Variables declarations
(declare-fun tmp () Int)
(declare-fun v_int_54_2217 () Int)
(declare-fun mp1_2206 () (Array Int Int))
(declare-fun mp2_2239 () (Array Int Int))
(declare-fun ub0 () (Array Int Int))
(declare-fun receiver () Int)
(declare-fun amount () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= (select ub0 tmp) (+ amount v_int_54_2217)))
(assert (= mp1_2206 (store ub0 tmp v_int_54_2217)))
(assert (= mp2_2239 (store mp1_2206 receiver (+ (select mp1_2206 receiver) amount))))
(assert (not (= (select mp2_2239 receiver) (+ (select ub0 receiver) amount))))
;Negation of Consequence
(assert (not false))
(check-sat)
