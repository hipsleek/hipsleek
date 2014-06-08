(set-logic QF_S)
(set-info :source |
C. Enea, O. Lengal, M. Sighireanu, and T. Vojnar
[Compositional Entailment Checking for a Fragment of Separation Logic]
http://www.liafa.univ-paris-diderot.fr/spen
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort SL2_t 0)

; fields
(declare-fun n1 () (Field SL2_t SL2_t))
(declare-fun n2 () (Field SL2_t SL2_t))

; one-level skip list (i.e. a SLL)
(define-fun skl1 ((?hd SL2_t) (?ex SL2_t)) Space
  (tospace (or (= ?hd ?ex)
  (exists ((?tl SL2_t))
  (tobool (ssep
    (pto ?hd (sref (ref n2 nil) (ref n1 ?tl)))
    (skl1 ?tl ?ex))
)))))

; two-level skip list
(define-fun skl2 ((?hd SL2_t) (?ex SL2_t)) Space
  (tospace (or (= ?hd ?ex)
  (exists ((?tl SL2_t) (?Z1 SL2_t))
  (tobool (ssep
    (pto ?hd (sref (ref n2 ?tl) (ref n1 ?Z1)))
    (skl1 ?Z1 ?tl)
    (skl2 ?tl ?ex))
)))))

; variables
(declare-fun x1 () SL2_t)
(declare-fun x1_1 () SL2_t)
(declare-fun x1_2 () SL2_t)
(declare-fun x1_3 () SL2_t)
(declare-fun x1_4 () SL2_t)
(declare-fun x2 () SL2_t)
(declare-fun x3 () SL2_t)
(declare-fun x3_1 () SL2_t)
(declare-fun x3_2 () SL2_t)

(assert (tobool (ssep
  (pto x1 (sref (ref n2 x2) (ref n1 x1_1)))
    (pto x1_1 (sref (ref n2 nil) (ref n1 x1_2)))
    (skl1 x1_2 x2)
  (pto x2 (sref (ref n2 nil) (ref n1 nil)))
)))

(assert (not
  (tobool (skl2 x1 nil))
))

; check whether the negation of the entailment is satisfiable
(check-sat)
