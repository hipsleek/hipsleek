(set-logic QF_S)
(set-info :source |
C. Enea, O. Lengal, M. Sighireanu, and T. Vojnar
[Compositional Entailment Checking for a Fragment of Separation Logic]
http://www.liafa.univ-paris-diderot.fr/spen
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(set-info :version "2014-05-28")


(declare-sort Sll_t 0)

(declare-fun next () (Field Sll_t Sll_t))

; singly-linked list
(define-fun ls ((?in Sll_t) (?out Sll_t))
  Space (tospace (or (= ?in ?out) 
    (exists ((?u Sll_t)) (and (distinct ?in ?out) (tobool (ssep
      (pto ?in (ref next ?u))
      (ls ?u ?out))
))))))

(declare-fun y_emp () Sll_t)
(declare-fun w_emp () Sll_t)

(assert
    (tobool (ls y_emp w_emp)
    )
)
(assert
  (not
    (tobool (ls y_emp w_emp))
))

(check-sat)
