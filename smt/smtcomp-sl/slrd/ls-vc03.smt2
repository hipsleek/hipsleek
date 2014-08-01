(set-logic QF_S)
(set-info :source |
C. Enea, O. Lengal, M. Sighireanu, and T. Vojnar
[Compositional Entailment Checking for a Fragment of Separation Logic]
http://www.liafa.univ-paris-diderot.fr/spen
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort Sll_t 0)

(declare-fun next () (Field Sll_t Sll_t))

; singly-linked list
(define-fun lso ((?in Sll_t) (?out Sll_t))
  Space (tospace (or (= ?in ?out) 
    (exists ((?u Sll_t)) (tobool (ssep
      (pto ?in (ref next ?u))
      (lso ?u ?out))
)))))

(declare-fun x_emp () Sll_t)
(declare-fun y_emp () Sll_t)
(declare-fun w_emp () Sll_t)
(declare-fun z_emp () Sll_t)
(declare-fun u_emp () Sll_t)
(declare-fun v_emp () Sll_t)
(declare-fun r_emp () Sll_t)
(declare-fun s_emp () Sll_t)
(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)
(assert
    (tobool (ssep (pto x_emp (ref next y_emp)) 
                  (index alpha2 (lso y_emp w_emp))
                  (index alpha3 (lso w_emp z_emp))
                  (pto z_emp (ref next u_emp))
                  (pto u_emp (ref next v_emp))
                  (index alpha4 (lso v_emp r_emp))
                  (pto r_emp (ref next s_emp))
            )
    )
)
(assert
  (not
    (tobool (index alpha1 (lso x_emp s_emp)))
))

(check-sat)
