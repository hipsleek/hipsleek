(set-logic QF_S)
(set-info :source |
C. Enea, O. Lengal, M. Sighireanu, and T. Vojnar
[Compositional Entailment Checking for a Fragment of Separation Logic]
http://www.liafa.univ-paris-diderot.fr/spen
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


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
(declare-fun x2_1 () SL3_t)
(declare-fun x2_1_1 () SL3_t)
(declare-fun x2_2 () SL3_t)
(declare-fun x2_2_1 () SL3_t)
(declare-fun x3 () SL3_t)

;
; two 1-field unfolding of skl3(x1,nil) for last node
; exp: unsat
;
(assert (tobool (ssep
  (skl3 x1 x2)
  (pto x2 (sref (ref n3 nil) (ref n2 x2_2) (ref n1 x2_1)))
  (pto x2_2 (sref (ref n3 nil) (ref n2 nil) (ref n1 x2_2_1)))
  (pto x2_1 (sref (ref n3 nil) (ref n2 nil) (ref n1 x2_1_1)))
  (pto x2_1_1 (sref (ref n3 nil) (ref n2 nil) (ref n1 x2_2)))
  (pto x2_2_1 (sref (ref n3 nil) (ref n2 nil) (ref n1 nil)))
)))

(assert (not
  (tobool (skl3 x1 nil))
))

; check whether the negation of the entailment is satisfiable
(check-sat)
