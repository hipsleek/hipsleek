(set-logic QF_SLRD)

(declare-sort NLL_lvl1_t 0)
(declare-sort NLL_lvl2_t 0)

; 'next' selector of level 1
(declare-fun next1 () (Field NLL_lvl1_t NLL_lvl1_t))
; 'next' selector of level 2
(declare-fun next2 () (Field NLL_lvl2_t NLL_lvl2_t))
; the bridge from level 2 to level 1
(declare-fun down () (Field NLL_lvl2_t NLL_lvl1_t))

; singly-linked list
(define-fun lso ((?in NLL_lvl1_t) (?out NLL_lvl1_t))
  Space (tospace (or (= ?in ?out) 
    (exists ((?u NLL_lvl1_t)) (tobool (ssep
      (pto ?in (ref next1 ?u))
      (lso ?u ?out))
)))))

; singly-linked list of singly-linked lists
(define-fun nll ((?in NLL_lvl2_t) (?out NLL_lvl2_t) (?boundary NLL_lvl1_t))
  Space (tospace (or (= ?in ?out)
    (exists ((?u NLL_lvl2_t) (?Z1 NLL_lvl1_t)) (tobool (ssep
      (pto ?in (sref
        (ref next2 ?u)
        (ref down ?Z1)))
      (lso ?Z1 ?boundary)
      (nll ?u ?out ?boundary))
)))))

(declare-fun x1 () NLL_lvl2_t)
(declare-fun x1_1 () NLL_lvl1_t)
(declare-fun x2 () NLL_lvl2_t)
(declare-fun x2_1 () NLL_lvl1_t)

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)

;
; (bad) unfoldings of nll(x1,nil,nil)
; exp: sat
;
(assert (tobool (ssep
  (pto x1 (sref
    (ref next2 x2)
    (ref down x1_1)))
  (pto x1_1 (ref next1 x2_1))
  (pto x2 (sref
    (ref next2 nil)
    (ref down x2_1)))
  (index alpha2 (lso x2_1 nil))
)))

(assert (not (tobool (index alpha3
  (nll x1 nil nil)
))))

(check-sat)

