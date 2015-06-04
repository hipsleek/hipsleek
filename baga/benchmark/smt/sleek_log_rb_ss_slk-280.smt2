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





































































































































































































































































































































































(declare-fun xprm () node)
(declare-fun cl12 () Int)
(declare-fun r38 () node)
(declare-fun flted290 () Int)
(declare-fun flted291 () Int)
(declare-fun flted292 () Int)
(declare-fun nr38 () Int)
(declare-fun bhl38 () Int)
(declare-fun bhr38 () Int)
(declare-fun a () Int)
(declare-fun x5 () node)
(declare-fun x () node)
(declare-fun aprm () Int)
(declare-fun v58 () Int)
(declare-fun nl38 () Int)
(declare-fun l38 () node)
(declare-fun bh15 () Int)
(declare-fun n11 () Int)
(declare-fun cl () Int)
(declare-fun bh () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xprm l38)
(= nr38 0)
(= bhr38 1)
(<= cl12 1)
(<= 0 cl12)
(<= 1 bh15)
(<= 0 n11)
(= cl12 0)
(= l38 nil)
(= nl38 0)
(= bhl38 1)
(= r38 nil)
(= flted290 1)
(= flted291 0)
(= flted292 0)
(= cl 1)
(= n (+ (+ nr38 1) nl38))
(= bhl38 bh)
(= bhr38 bh)
(distinct x5 nil)
(<= cl 1)
(<= 0 cl)
(= aprm a)
(= x5 x)
(= aprm v58)
(= bh15 1)
(= n11 0)
(tobool  
(pto x5 (sref (ref val v58) (ref color flted290) (ref left l38) (ref right r38) ))
 )
)
)

(assert (not 
(exists ((flted331 Int)(flted332 Int)(bh32 Int)(h37 Int))(and 
(= cl 0)
(<= bh32 h37)
(<= bh (+ bh32 1))
(= flted331 0)
(= (+ flted332 1) n)
(<= cl 1)
(<= 0 cl)
(<= 1 bh)
(<= 0 n)
(tobool  
(rb xprm flted332 flted331 bh32)
 )
))
))

(check-sat)