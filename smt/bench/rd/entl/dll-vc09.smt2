(set-logic QF_S)
(set-info :source |
C. Enea, O. Lengal, M. Sighireanu, and T. Vojnar
[Compositional Entailment Checking for a Fragment of Separation Logic]
http://www.liafa.univ-paris-diderot.fr/spen
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unknown)
(set-info :version "2014-05-28")


(declare-sort Dll_t 0)

(declare-fun next () (Field Dll_t Dll_t))
(declare-fun prev () (Field Dll_t Dll_t))

; doubly-linked list
(define-fun dll ((?fr Dll_t) (?bk Dll_t) (?pr Dll_t) (?nx Dll_t))
  Space (tospace (or (and (= ?fr ?nx) (= ?bk ?pr)) 
    (exists ((?u Dll_t)) (and (distinct ?fr ?nx) (tobool (ssep
      (pto ?fr (sref (ref next ?u) (ref prev ?pr)))
      (dll ?u ?bk ?fr ?nx))
))))))

(declare-fun x () Dll_t)
(declare-fun y () Dll_t)
(declare-fun z () Dll_t)
(declare-fun x1 () Dll_t)
(declare-fun x2 () Dll_t)
(declare-fun x3 () Dll_t)
(declare-fun x4 () Dll_t)

;
; four unfoldings of dll(x,y,nil,z)
;
(assert
    (and (distinct z x) (distinct z x1) (distinct z x2) (distinct z x3)
         (distinct z x4) (distinct z y)
    (tobool (ssep (pto x  (sref (ref next x1) (ref prev nil))) 
                  (pto x1 (sref (ref next x2) (ref prev x)))
                  (pto x2 (sref (ref next x3) (ref prev x1)))
                  (pto x3 (sref (ref next x4) (ref prev x2)))
                  (pto x4 (sref (ref next y ) (ref prev x3)))
                  (pto y  (sref (ref next z ) (ref prev x4)))
            )
    ))
)
(assert
  (not
    (tobool (dll x y nil z))
))

(check-sat)
