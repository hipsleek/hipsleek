(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun rr_primed () Int)
(declare-fun rl_primed () Int)
(declare-fun rrm () Int)
(declare-fun rr () Int)
(declare-fun rlm () Int)
(declare-fun rl () Int)
(declare-fun ln_3187 () Int)
(declare-fun flted_32_3188 () Int)
(declare-fun l_primed () Int)
(declare-fun lm () Int)
(declare-fun ln () Int)
(declare-fun l () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= rr_primed rr))
(assert (= rl_primed rl))
(assert (or (and (and (< rr 1) (= rrm 0)) (= flted_32_3188 0)) (and (and (<= 1 flted_32_3188) (<= 1 rrm)) (> rr 0))))
(assert (or (and (and (< rl 1) (= rlm 0)) (= ln_3187 0)) (and (and (<= 1 ln_3187) (<= 1 rlm)) (> rl 0))))
(assert (= ln_3187 ln))
(assert (= flted_32_3188 (+ 1 ln)))
(assert (= l_primed l))
(assert (or (and (and (< l 1) (= lm 0)) (= ln 0)) (and (and (<= 1 ln) (<= 1 lm)) (> l 0))))
;Negation of Consequence
(assert (not (or (= lm 0) (or (= ln 0) (< l 1)))))
(check-sat)