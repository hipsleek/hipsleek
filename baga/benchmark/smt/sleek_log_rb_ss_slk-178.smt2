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





































































































































































































































































































































































(declare-fun Anon23 () Int)
(declare-fun res () Int)
(declare-fun v45 () Int)
(declare-fun xprm () node)
(declare-fun r33 () node)
(declare-fun l33 () node)
(declare-fun x3 () node)
(declare-fun x () node)
(declare-fun bhl33 () Int)
(declare-fun nl33 () Int)
(declare-fun flted266 () Int)
(declare-fun nr33 () Int)
(declare-fun bhr33 () Int)
(declare-fun Anon24 () Int)
(declare-fun n9 () Int)
(declare-fun bh7 () Int)
(declare-fun cl7 () Int)
(declare-fun cl () Int)
(declare-fun bh () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= res v45)
(= xprm r33)
(= l33 nil)
(<= cl 1)
(<= 0 cl)
(distinct x nil)
(= x3 x)
(= bh (+ bhl33 1))
(= bhl33 bhr33)
(= n (+ (+ nr33 1) nl33))
(= cl 0)
(= flted266 0)
(= n9 nr33)
(= cl7 Anon24)
(= bh7 bhr33)
(<= 0 nr33)
(<= 1 bhr33)
(<= 0 Anon24)
(<= Anon24 1)
(= cl7 0)
(<= 0 n9)
(<= 1 bh7)
(<= 0 cl7)
(<= cl7 1)
(tobool (ssep 
(pto x3 (sref (ref val v45) (ref color flted266) (ref left l33) (ref right r33) ))
(rb l33 nl33 Anon23 bhl33)
(rb r33 n9 cl7 bh7)
) )
)
)

(assert (not 
(exists ((bh13 Int)(flted283 Int)(cl11 Int))(and 
(= bh13 bh)
(<= cl11 1)
(<= 0 cl11)
(= cl 1)
(= (+ flted283 1) n)
(<= cl 1)
(<= 0 cl)
(<= 1 bh)
(<= 0 n)
(tobool  
(rb xprm flted283 cl11 bh13)
 )
))
))

(check-sat)