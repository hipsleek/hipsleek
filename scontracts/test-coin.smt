; ;Variables declarations
; (declare-fun tmp () Int)
; (declare-fun v_int_54_2217 () Int)
; (declare-fun mp1_2206 () (Array Int Int))
; (declare-fun mp2_2239 () (Array Int Int))
; (declare-fun ub0 () (Array Int Int))
; (declare-fun receiver () Int)
; (declare-fun amount () Int)
; ;Relations declarations
; ;Axioms assertions
; ;Antecedent
; (assert (= (select ub0 tmp) (+ amount v_int_54_2217)))             ; ub0[tmp] = amount + v_int_54_2217
; (assert (= mp1_2206 (store ub0 tmp v_int_54_2217)))                ; mp1_2206 = ub0 & mp1_2206[tmp] := v_int_54_2217
; (assert (= mp2_2239 (store mp1_2206 receiver (+ (select mp1_2206 receiver) amount)))) ; mp2_2239 = mp1_2206 & mp1_2239[receiver] = mp1_2206[receiver] + amount
; (assert (not (= (select mp2_2239 receiver) (+ (select ub0 receiver) amount))))        ; mp2_2239[receiver] = ub0[receiver] + amount.
; ;Negation of Consequence
; (assert (not false))
; (check-sat)


;Variables declarations
(declare-fun mp2_2339 () (Array Int Int))
(declare-fun val_2307 () Int)
(declare-fun mp1_2306 () (Array Int Int))
(declare-fun mp1 () (Array Int Int))
(declare-fun receiver_primed () Int)
(declare-fun amount () Int)
(declare-fun msg_35_primed () Int)
(declare-fun balances_34 () (Array Int Int))
(declare-fun receiver () Int)
(declare-fun sender () Int)
(declare-fun v_int_67_2317 () Int)
(declare-fun amount_primed () Int)
(declare-fun val () Int)
(declare-fun mp1111 () (Array Int Int))
(declare-fun ub0 () (Array Int Int))
(declare-fun mp1111_2325 () (Array Int Int))
(declare-fun mp2_2316 () (Array Int Int))
(declare-fun msg_35 () Int)
(declare-fun balances_34_primed () (Array Int Int))
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= mp2_2339 (store mp1111_2325 receiver_primed (+ amount_primed val_2307))))
(assert (= (select mp1_2306 receiver_primed) val_2307))
(assert (= mp1_2306 mp2_2316))
(assert (= mp2_2316 (store mp1111 sender v_int_67_2317)))
(assert (= (select mp1 sender) val))
(assert (= mp1 ub0))
(assert (= receiver_primed receiver))
(assert (= amount_primed amount))
(assert (= msg_35_primed msg_35))
(assert (= balances_34_primed balances_34))
(assert (not (= receiver sender)))
(assert (= (+ v_int_67_2317 amount_primed) val))
(assert (= mp1111 ub0))
(assert (= mp1111_2325 mp2_2316))
(assert (> msg_35 0))
;Negation of Consequence
(assert (not (= msg_35 balances_34_primed)))
(check-sat)
