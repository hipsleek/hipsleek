(set-logic QF_SLRD)

(declare-sort SL3_t 0)

; fields
(declare-fun n1 () (Field SL3_t SL3_t))
(declare-fun n2 () (Field SL3_t SL3_t))
(declare-fun n3 () (Field SL3_t SL3_t))

; one-level skip list (i.e. a SLL)
(define-fun skl1 ((?hd SL3_t) (?ex SL3_t)) Space
  (tospace (or (= ?hd ?ex)
  (exists ((?tl SL3_t))
  (tobool (ssep
    (pto ?hd (sref (ref n3 nil) (ref n2 nil) (ref n1 ?tl)))
    (skl1 ?tl ?ex))
)))))

; two-level skip list
(define-fun skl2 ((?hd SL3_t) (?ex SL3_t)) Space
  (tospace (or (= ?hd ?ex)
  (exists ((?tl SL3_t) (?Z1 SL3_t))
  (tobool (ssep
    (pto ?hd (sref (ref n3 nil) (ref n2 ?tl) (ref n1 ?Z1)))
    (skl1 ?Z1 ?tl)
    (skl2 ?tl ?ex))
)))))

; three-level skip list
(define-fun skl3 ((?hd SL3_t) (?ex SL3_t)) Space
  (tospace (or (= ?hd ?ex)
  (exists ((?tl SL3_t) (?Z1 SL3_t) (?Z2 SL3_t))
  (tobool (ssep
    (pto ?hd (sref (ref n3 ?tl) (ref n2 ?Z2) (ref n1 ?Z1)))
    (skl1 ?Z1 ?Z2)
    (skl2 ?Z2 ?tl)
    (skl3 ?tl ?ex))
)))))

; variables
(declare-fun x1 () SL3_t)
(declare-fun x2 () SL3_t)
(declare-fun x2_0_1 () SL3_t)
(declare-fun x2_1 () SL3_t)
(declare-fun x2_2 () SL3_t)
(declare-fun x2_2_1 () SL3_t)
(declare-fun x2_2_2 () SL3_t)
(declare-fun x2_3 () SL3_t)
(declare-fun x2_3_1 () SL3_t)
(declare-fun x2_4 () SL3_t)
(declare-fun x3 () SL3_t)

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)
(declare-fun alpha5 () SetLoc)
(declare-fun alpha6 () SetLoc)
(declare-fun alpha7 () SetLoc)
(declare-fun alpha8 () SetLoc)

;
; level 2 insertion in the middle
; expected: holds
;
(assert (tobool (ssep
  (index alpha1 (skl3 x1 x2))
  (pto x2 (sref (ref n3 x3) (ref n2 x2_1) (ref n1 x2_0_1)))
      (index alpha4 (skl1 x2_0_1 x2_1))
    (index alpha3 (skl2 x2_1 x2_2))
    (pto x2_2 (sref (ref n3 nil) (ref n2 x2_3) (ref n1 x2_2_1)))
      (index alpha6 (skl1 x2_2_1 x2_2_2))
      (pto x2_2_2 (sref (ref n3 nil) (ref n2 nil) (ref n1 x2_3)))
    (pto x2_3 (sref (ref n3 nil) (ref n2 x2_4) (ref n1 x2_3_1)))
      (index alpha7 (skl1 x2_3_1 x2_4))
      (index alpha8 (skl2 x2_4 x3))
  (index alpha2 (skl3 x3 nil))
)))

(assert (not
  (tobool (index alpha5 (skl3 x1 nil)))
))

; check whether the negation of the entailment is satisfiable
(check-sat)
