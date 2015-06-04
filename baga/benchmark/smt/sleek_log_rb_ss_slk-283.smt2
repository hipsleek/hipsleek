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





































































































































































































































































































































































(declare-fun Anon28 () Int)
(declare-fun xprm () node)
(declare-fun l39 () node)
(declare-fun r39 () node)
(declare-fun flted293 () Int)
(declare-fun nr39 () Int)
(declare-fun bhr39 () Int)
(declare-fun a () Int)
(declare-fun x6 () node)
(declare-fun x () node)
(declare-fun aprm () Int)
(declare-fun v59 () Int)
(declare-fun nl39 () Int)
(declare-fun bhl39 () Int)
(declare-fun Anon27 () Int)
(declare-fun n11 () Int)
(declare-fun bh15 () Int)
(declare-fun cl12 () Int)
(declare-fun cl () Int)
(declare-fun bh () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xprm l39)
(= r39 nil)
(= flted293 0)
(= cl 0)
(= n (+ (+ nr39 1) nl39))
(= bhl39 bhr39)
(= bh (+ bhl39 1))
(distinct x6 nil)
(<= cl 1)
(<= 0 cl)
(= aprm a)
(= x6 x)
(= aprm v59)
(= n11 nl39)
(= cl12 Anon27)
(= bh15 bhl39)
(<= 0 nl39)
(<= 1 bhl39)
(<= 0 Anon27)
(<= Anon27 1)
(= cl12 0)
(<= 0 n11)
(<= 1 bh15)
(<= 0 cl12)
(<= cl12 1)
(tobool (ssep 
(pto x6 (sref (ref val v59) (ref color flted293) (ref left l39) (ref right r39) ))
(rb r39 nr39 Anon28 bhr39)
(rb l39 n11 cl12 bh15)
) )
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