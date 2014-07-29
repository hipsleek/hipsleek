(set-logic QF_SLRD)

(declare-sort Sll_t 0)

(declare-fun next () (Field Sll_t Sll_t))

; singly-linked list
(define-fun lso ((?in Sll_t) (?out Sll_t))
  Space (tospace (or (= ?in ?out) 
    (exists ((?u Sll_t)) (tobool (ssep
      (pto ?in (ref next ?u))
      (lso ?u ?out))
)))))

(declare-fun y_emp () Sll_t)
(declare-fun w_emp () Sll_t)
(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(assert
    (tobool (index alpha2 (lso y_emp w_emp))
    )
)
(assert
  (not
    (tobool (index alpha1 (lso y_emp w_emp)))
))

(check-sat)
