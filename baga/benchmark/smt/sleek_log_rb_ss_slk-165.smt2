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





































































































































































































































































































































































(declare-fun v44 () Int)
(declare-fun r32 () node)
(declare-fun v49_21195 () node)
(declare-fun bh9_21194 () Int)
(declare-fun flted273_21192 () Int)
(declare-fun flted274_21193 () Int)
(declare-fun bh8 () Int)
(declare-fun cl8 () Int)
(declare-fun n10 () Int)
(declare-fun flted265 () Int)
(declare-fun flted264 () Int)
(declare-fun flted263 () Int)
(declare-fun n () Int)
(declare-fun nl32 () Int)
(declare-fun nr32 () Int)
(declare-fun bhl32 () Int)
(declare-fun bhr32 () Int)
(declare-fun bh () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun cl () Int)
(declare-fun l32 () node)


(assert 
(exists ((flted273 Int)(flted274 Int)(bh9 Int)(v49 node))(and 
;lexvar(<= cl8 1)
(<= 0 cl8)
(<= 1 bh8)
(<= 0 n10)
(= cl8 0)
(<= bh9 bh8)
(<= bh8 (+ bh9 1))
(= flted273 0)
(= (+ flted274 1) n10)
(<= flted264 1)
(<= 0 flted264)
(<= 1 bhl32)
(<= 0 nl32)
(= bh8 bhl32)
(= cl8 flted264)
(= n10 nl32)
(= flted265 1)
(= flted264 0)
(= flted263 0)
(= cl 1)
(= n (+ (+ nr32 1) nl32))
(= bhl32 bh)
(= bhr32 bh)
(= xprm x)
(distinct x nil)
(<= 0 cl)
(<= cl 1)
(distinct l32 nil)
(tobool (ssep 
(pto xprm (sref (ref val v44) (ref color flted265) (ref left l32) (ref right r32) ))
(rb r32 nr32 flted263 bhr32)
(rb v49 flted274 flted273 bh9)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val33prm) (ref color color34prm) (ref left left33prm) (ref right right33prm) ))
 )
)
))

(check-sat)