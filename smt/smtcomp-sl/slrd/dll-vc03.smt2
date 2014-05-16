(set-logic QF_S)
(set-info :source |
C. Enea, O. Lengal, M. Sighireanu, and T. Vojnar
[Compositional Entailment Checking for a Fragment of Separation Logic]
http://www.liafa.univ-paris-diderot.fr/spen
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)

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
(declare-fun w_emp () Dll_t)
(declare-fun y_emp () Dll_t)
(declare-fun u_emp () Dll_t)
(declare-fun z_emp () Dll_t)
(declare-fun alpha1 () SetLoc)

;
; three unfoldings of dll(x,u,z,z)
; exp: unsat
;
(assert
    (tobool (ssep (pto x_emp (sref (ref next w_emp) (ref prev z_emp))) 
                  (pto w_emp (sref (ref next y_emp) (ref prev x_emp)))
                  (pto y_emp (sref (ref next u_emp) (ref prev w_emp)))
                  (pto u_emp (sref (ref next z_emp) (ref prev y_emp)))
            )
    )
)
(assert
  (not
    (tobool (index alpha1 (dll x_emp u_emp z_emp z_emp)))
))

(check-sat)
