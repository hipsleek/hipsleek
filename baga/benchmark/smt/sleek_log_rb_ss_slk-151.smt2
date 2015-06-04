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





































































































































































































































































































































































(declare-fun l32 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun bhr32 () Int)
(declare-fun bhl32 () Int)
(declare-fun bh () Int)
(declare-fun n () Int)
(declare-fun nl32 () Int)
(declare-fun cl () Int)
(declare-fun flted263 () Int)
(declare-fun flted264 () Int)
(declare-fun flted265 () Int)
(declare-fun tmpprm () Int)
(declare-fun v44 () Int)
(declare-fun v102prm () node)
(declare-fun nr32 () Int)
(declare-fun r32 () node)
(declare-fun cl7 () Int)
(declare-fun bh7 () Int)
(declare-fun n9 () Int)


(assert 
(and 
;lexvar(= r32 nil)
(= nr32 0)
(= bhr32 1)
(= l32 nil)
(<= cl 1)
(<= 0 cl)
(distinct x nil)
(= xprm x)
(= bhr32 bh)
(= bhl32 bh)
(= n (+ (+ nr32 1) nl32))
(= cl 1)
(= flted263 0)
(= flted264 0)
(= flted265 1)
(= tmpprm v44)
(= v102prm r32)
(= cl7 0)
(= bh7 1)
(= n9 0)
(tobool (ssep 
(pto xprm (sref (ref val v44) (ref color flted265) (ref left l32) (ref right r32) ))
(rb l32 nl32 flted264 bhl32)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)