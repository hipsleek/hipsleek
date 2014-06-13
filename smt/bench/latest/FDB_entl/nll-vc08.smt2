(set-logic QF_S)
(set-info :source |
C. Enea, O. Lengal, M. Sighireanu, and T. Vojnar
[Compositional Entailment Checking for a Fragment of Separation Logic]
http://www.liafa.univ-paris-diderot.fr/spen
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


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
    (exists ((?u NLL_lvl1_t)) 
      (and (distinct ?in ?out) 
           (tobool (ssep
           (pto ?in (ref next1 ?u))
           (lso ?u ?out))
))))))

; singly-linked list of singly-linked lists
(define-fun nll ((?in NLL_lvl2_t) (?out NLL_lvl2_t) (?boundary NLL_lvl1_t))
  Space (tospace (or (= ?in ?out)
    (exists ((?u NLL_lvl2_t) (?Z1 NLL_lvl1_t)) 
      (and (distinct ?in ?out) 
           (tobool (ssep
           (pto ?in (sref (ref next2 ?u) (ref down ?Z1)))
           (lso ?Z1 ?boundary)
           (nll ?u ?out ?boundary))
))))))

(declare-fun x1 () NLL_lvl2_t)
(declare-fun x2 () NLL_lvl2_t)
(declare-fun x2_1 () NLL_lvl1_t)
(declare-fun x2_2 () NLL_lvl1_t)
(declare-fun x2_3 () NLL_lvl1_t)
(declare-fun x3 () NLL_lvl2_t)

;
; one unfolding in middle (inner list) of nll(x1,nil,nil)
; exp: unsat
;
(assert (tobool (ssep
  (nll x1 x2 nil)
  (pto x2 (sref
    (ref next2 x3)
    (ref down x2_1)))
  (lso x2_1 x2_2)
  (pto x2_2 (ref next1 x2_3))
  (lso x2_3 nil)
  (nll x3 nil nil)
)))

(assert (not (tobool 
  (nll x1 nil nil)
)))

(check-sat)

