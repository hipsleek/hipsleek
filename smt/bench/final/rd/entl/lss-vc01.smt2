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

(declare-fun next1 () (Field Sll_t Sll_t))
(declare-fun next2 () (Field Sll_t Sll_t))

; singly-linked list
(define-fun lsso ((?in Sll_t) (?out Sll_t))
  Space (tospace (or (= ?in ?out) 
    (exists ((?u Sll_t)) (tobool (ssep
      (pto ?in (sref
				(ref next1 ?u)
				(ref next2 ?u)))
      (lsso ?u ?out))
)))))

(declare-fun x_emp () Sll_t)
(declare-fun y_emp () Sll_t)
(declare-fun z_emp () Sll_t)

(assert
    (tobool (ssep 
		(pto x_emp (sref (ref next1 y_emp) (ref next2 y_emp))) 
		(pto y_emp (sref (ref next1 z_emp) (ref next2 z_emp)))
)))
(assert
  (not
    (tobool (lsso x_emp z_emp))
))

(check-sat)
