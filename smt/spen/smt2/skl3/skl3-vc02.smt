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
(declare-fun x1_2 () SL3_t)
(declare-fun x2 () SL3_t)

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)

;
; bad two 1-field unfolding of skl3(x1,nil)
; exp: sat
;
(assert (tobool (ssep
  (pto x1 (sref (ref n3 x2) (ref n2 x1_2) (ref n1 x2)))
  (index alpha2 (skl2 x1_2 x2))
  (index alpha3 (skl3 x2 nil))
)))

(assert (not
  (tobool (index alpha1 (skl3 x1 nil)))
))

; check whether the negation of the entailment is satisfiable
(check-sat)
