(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


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





































































































































































































































































































































































(declare-fun res () Int)
(declare-fun v44 () Int)
(declare-fun xprm () node)
(declare-fun cl7 () Int)
(declare-fun l32 () node)
(declare-fun x2 () node)
(declare-fun x () node)
(declare-fun bhr32 () Int)
(declare-fun bhl32 () Int)
(declare-fun nl32 () Int)
(declare-fun flted263 () Int)
(declare-fun flted264 () Int)
(declare-fun flted265 () Int)
(declare-fun nr32 () Int)
(declare-fun r32 () node)
(declare-fun bh7 () Int)
(declare-fun n9 () Int)
(declare-fun cl () Int)
(declare-fun bh () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= res v44)
(= xprm r32)
(= nl32 0)
(= bhl32 1)
(<= cl7 1)
(<= 0 cl7)
(<= 1 bh7)
(<= 0 n9)
(= cl7 0)
(= r32 nil)
(= nr32 0)
(= bhr32 1)
(= l32 nil)
(<= cl 1)
(<= 0 cl)
(distinct x nil)
(= x2 x)
(= bhr32 bh)
(= bhl32 bh)
(= n (+ (+ nr32 1) nl32))
(= cl 1)
(= flted263 0)
(= flted264 0)
(= flted265 1)
(= bh7 1)
(= n9 0)
(tobool  
(pto x2 (sref (ref val v44) (ref color flted265) (ref left l32) (ref right r32) ))
 )
)
)

(assert (not 
(exists ((flted284 Int)(flted285 Int)(bh14 Int))(and 
(= cl 0)
(<= bh14 bh)
(<= bh (+ bh14 1))
(= flted284 0)
(= (+ flted285 1) n)
(<= cl 1)
(<= 0 cl)
(<= 1 bh)
(<= 0 n)
(tobool  
(rb xprm flted285 flted284 bh14)
 )
))
))

(check-sat)