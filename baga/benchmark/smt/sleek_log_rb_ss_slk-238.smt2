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





































































































































































































































































































































































(declare-fun Anon27 () Int)
(declare-fun l39 () node)
(declare-fun Anon28 () Int)
(declare-fun v121prm () node)
(declare-fun r39 () node)
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
(declare-fun v59 () Int)
(declare-fun aprm () Int)


(assert 
(and 
;lexvar(= v121prm r39)
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
(< v59 aprm)
(tobool (ssep 
(rb l39 nl39 Anon27 bhl39)
(pto xprm (sref (ref val v59) (ref color flted293) (ref left l39) (ref right r39) ))
(rb r39 nr39 Anon28 bhr39)
) )
)
)

(assert (not 
(and 
(<= cl16 1)
(<= 0 cl16)
(tobool  
(rb v121prm n13 cl16 bh21)
 )
)
))

(check-sat)