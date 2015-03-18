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

(declare-fun x_emp () Sll_t)
(declare-fun y_emp () Sll_t)
(declare-fun z_emp () Sll_t)
(declare-fun alpha1 () SetLoc)
(assert
    (tobool (ssep (pto x_emp (ref next y_emp)) 
                  (pto y_emp (ref next z_emp))
            )
    )
)
(assert
  (not
    (tobool (index alpha1 (lso x_emp z_emp)))
))

(check-sat)
