(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun x1_primed () Int)
(declare-fun x2_primed () Int)
(declare-fun v_bool_92_1414_primed () Int)
(declare-fun s1 () Int)
(declare-fun b1 () Int)
(declare-fun n1 () Int)
(declare-fun s2 () Int)
(declare-fun b2 () Int)
(declare-fun n2 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= x1_primed x1))
(assert (= x2_primed x2))
(assert (> x2_primed 0))
(assert (not (> v_bool_92_1414_primed 0)))
(assert (or (and (and (= b1 s1) (= n1 1)) (> x1 0)) (and (and (<= s1 b1) (<= 2 n1)) (> x1 0))))
(assert (or (and (and (= b2 s2) (= n2 1)) (> x2 0)) (and (and (<= s2 b2) (<= 2 n2)) (> x2 0))))
(assert (not (= x1 x2)))
;Negation of Consequence
(assert (not false))
(check-sat)