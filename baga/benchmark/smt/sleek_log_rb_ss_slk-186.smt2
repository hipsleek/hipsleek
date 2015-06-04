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





































































































































































































































































































































































(declare-fun v56_22608 () Int)
(declare-fun l36_22609 () node)
(declare-fun r36_22612 () node)
(declare-fun x () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun xprm () node)
(declare-fun bhr36_22614 () Int)
(declare-fun bhl36_22611 () Int)
(declare-fun bh () Int)
(declare-fun n () Int)
(declare-fun nl36_22610 () Int)
(declare-fun nr36_22613 () Int)
(declare-fun cl () Int)
(declare-fun flted286_22605 () Int)
(declare-fun flted287_22606 () Int)
(declare-fun flted288_22607 () Int)


(assert 
(exists ((flted286 Int)(flted287 Int)(flted288 Int)(v56 Int)(l36 node)(nl36 Int)(bhl36 Int)(r36 node)(nr36 Int)(bhr36 Int))(and 
;lexvar(= xprm x)
(= aprm a)
(<= 0 cl)
(<= cl 1)
(distinct xprm nil)
(= bhr36 bh)
(= bhl36 bh)
(= n (+ (+ nr36 1) nl36))
(= cl 1)
(= flted286 0)
(= flted287 0)
(= flted288 1)
(tobool (ssep 
(pto xprm (sref (ref val v56) (ref color flted288) (ref left l36) (ref right r36) ))
(rb l36 nl36 flted287 bhl36)
(rb r36 nr36 flted286 bhr36)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val34prm) (ref color color35prm) (ref left left34prm) (ref right right34prm) ))
 )
)
))

(check-sat)