(set-logic QF_SLRD)

(declare-sort Dll_t 0)

(declare-fun next () (Field Dll_t Dll_t))
(declare-fun prev () (Field Dll_t Dll_t))

; doubly-linked list
(define-fun dll ((?in Dll_t) (?ex Dll_t) (?pr Dll_t) (?hd Dll_t))
  Space (tospace (or (and (= ?in ?pr) (= ?hd ?ex)) 
    (exists ((?u Dll_t)) (tobool (ssep
      (pto ?in (sref (ref next ?u) (ref prev ?pr)))
      (dll ?u ?ex ?in ?hd))
)))))

(declare-fun x_emp () Dll_t)
(declare-fun y_emp () Dll_t)
(declare-fun z_emp () Dll_t)
(declare-fun w_emp () Dll_t)
(declare-fun u_emp () Dll_t)
(declare-fun t_emp () Dll_t)
(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
;
; unfolding in the middle of dll(x,y,nil,z)
; exp: unsat
;
(assert
    (tobool (ssep (pto w_emp (sref (ref next t_emp) (ref prev u_emp))) 
                  (index alpha2 (dll x_emp u_emp nil w_emp))
                  (index alpha3 (dll t_emp y_emp w_emp z_emp))
            )
    )
)
(assert
  (not
    (tobool (index alpha1 (dll x_emp y_emp nil z_emp)))
))

(check-sat)
