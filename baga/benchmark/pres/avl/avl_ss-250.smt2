(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun lr_primed () Int)
(declare-fun ll_primed () Int)
(declare-fun lrm () Int)
(declare-fun lr () Int)
(declare-fun llm () Int)
(declare-fun ll () Int)
(declare-fun flted_50_4444 () Int)
(declare-fun lln () Int)
(declare-fun r_primed () Int)
(declare-fun rm () Int)
(declare-fun flted_50_4443 () Int)
(declare-fun r () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= lr_primed lr))
(assert (= ll_primed ll))
(assert (or (and (and (< lr 1) (= lrm 0)) (= flted_50_4444 0)) (and (and (<= 1 flted_50_4444) (<= 1 lrm)) (> lr 0))))
(assert (or (and (and (< ll 1) (= llm 0)) (= lln 0)) (and (and (<= 1 lln) (<= 1 llm)) (> ll 0))))
(assert (= (+ flted_50_4444 1) lln))
(assert (= (+ flted_50_4443 1) lln))
(assert (= r_primed r))
(assert (or (and (and (< r 1) (= rm 0)) (= flted_50_4443 0)) (and (and (<= 1 flted_50_4443) (<= 1 rm)) (> r 0))))
;Negation of Consequence
(assert (not (or (= rm 0) (or (= flted_50_4443 0) (< r 1)))))
(check-sat)