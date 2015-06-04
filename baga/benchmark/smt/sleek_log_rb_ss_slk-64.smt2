(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun color () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun rb ((?in node) (?n Int) (?cl Int) (?bh Int))
Space (tospace
(or
(or
(and 
(= ?in nil)
(= ?n 0)
(= ?bh 1)
(= ?cl 0)

)(exists ((?flted_12_38 Int)(?flted_12_39 Int)(?flted_12_40 Int))(and 
(= ?flted_12_40 1)
(= ?flted_12_39 0)
(= ?flted_12_38 0)
(= ?cl 1)
(= ?n (+ (+ ?nr 1) ?nl))
(= ?bhl ?bh)
(= ?bhr ?bh)
(tobool (ssep 
(pto ?in (sref (ref val ?v) (ref color ?flted_12_40) (ref left ?l) (ref right ?r) ))
(rb ?l ?nl ?flted_12_39 ?bhl)
(rb ?r ?nr ?flted_12_38 ?bhr)
) )
)))(exists ((?flted_13_41 Int))(and 
(= ?flted_13_41 0)
(= ?cl 0)
(= ?n (+ (+ ?nr 1) ?nl))
(= ?bhl ?bhr)
(= ?bh (+ ?bhl 1))
(tobool (ssep 
(pto ?in (sref (ref val ?v) (ref color ?flted_13_41) (ref left ?l) (ref right ?r) ))
(rb ?l ?nl ?Anon_14 ?bhl)
(rb ?r ?nr ?Anon_15 ?bhr)
) )
)))))





































































































































































































































































































































































(declare-fun v21 () Int)
(declare-fun nc () Int)
(declare-fun nc6 () Int)
(declare-fun Anon1 () node)
(declare-fun Anon8 () node)
(declare-fun nb6 () Int)
(declare-fun h21 () Int)
(declare-fun na6 () node)
(declare-fun na () node)
(declare-fun v49prm () Int)
(declare-fun v48prm () node)
(declare-fun r13 () node)
(declare-fun v47prm () node)
(declare-fun l13 () node)
(declare-fun flted123 () Int)
(declare-fun flted122 () Int)
(declare-fun h () Int)
(declare-fun flted120 () Int)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun flted121 () Int)
(declare-fun bhl13 () Int)
(declare-fun nb () Int)
(declare-fun nl13 () Int)
(declare-fun flted119 () Int)
(declare-fun flted118 () Int)
(declare-fun nr13 () Int)
(declare-fun bhr13 () Int)
(declare-fun Anon9 () Int)
(declare-fun n () Int)
(declare-fun bh () Int)
(declare-fun cl () Int)


(assert 
(and 
;lexvar(= nc6 n)
(= Anon1 Anon8)
(= nb6 nl13)
(= h21 h)
(= na6 na)
(= v49prm 1)
(= v48prm r13)
(= v47prm l13)
(distinct c nil)
(distinct b nil)
(= flted123 (+ 1 h))
(= flted122 0)
(= flted121 (+ 1 h))
(= flted120 0)
(= cprm c)
(= bprm b)
(= aprm a)
(= flted121 (+ bhl13 1))
(= bhl13 bhr13)
(= nb (+ (+ nr13 1) nl13))
(= flted119 0)
(= flted118 0)
(= n nr13)
(= cl Anon9)
(= bh bhr13)
(<= 0 nr13)
(<= 1 bhr13)
(<= 0 Anon9)
(<= Anon9 1)
(= cl 1)
(<= 0 n)
(<= 1 bh)
(<= 0 cl)
(<= cl 1)
(tobool (ssep 
(pto bprm (sref (ref val v21) (ref color flted118) (ref left l13) (ref right r13) ))
(rb c nc flted122 flted123)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)