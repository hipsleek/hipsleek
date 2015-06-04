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
(declare-fun r39 () node)
(declare-fun v86 () node)
(declare-fun v124prm () node)
(declare-fun l39 () node)
(declare-fun cl21 () Int)
(declare-fun flted327 () Int)
(declare-fun bh26 () Int)
(declare-fun cl19 () Int)
(declare-fun Anon27 () Int)
(declare-fun n14 () Int)
(declare-fun x () node)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun bh () Int)
(declare-fun bhl39 () Int)
(declare-fun bhr39 () Int)
(declare-fun n () Int)
(declare-fun nl39 () Int)
(declare-fun nr39 () Int)
(declare-fun cl () Int)
(declare-fun flted293 () Int)
(declare-fun aprm () Int)
(declare-fun v59 () Int)


(assert 
(and 
;lexvar(= v124prm l39)
(<= cl19 1)
(<= 0 cl19)
(<= 1 bh26)
(<= 0 n14)
(<= cl21 1)
(<= 0 cl21)
(= cl19 1)
(= (+ flted327 1) n14)
(<= Anon27 1)
(<= 0 Anon27)
(<= 1 bhl39)
(<= 0 nl39)
(= bh26 bhl39)
(= cl19 Anon27)
(= n14 nl39)
(= xprm x)
(= aprm a)
(<= 0 cl)
(<= cl 1)
(distinct xprm nil)
(= bh (+ bhl39 1))
(= bhl39 bhr39)
(= n (+ (+ nr39 1) nl39))
(= cl 0)
(= flted293 0)
(distinct v59 aprm)
(<= aprm v59)
(tobool (ssep 
(rb r39 nr39 Anon28 bhr39)
(pto xprm (sref (ref val v59) (ref color flted293) (ref left l39) (ref right r39) ))
(rb v86 flted327 cl21 bh26)
) )
)
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)