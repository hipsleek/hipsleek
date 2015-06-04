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





































































































































































































































































































































































(declare-fun v57_22659 () Int)
(declare-fun l37_22660 () node)
(declare-fun Anon25_22662 () Int)
(declare-fun r37_22664 () node)
(declare-fun Anon26_22666 () Int)
(declare-fun x () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun xprm () node)
(declare-fun bh () Int)
(declare-fun bhl37_22663 () Int)
(declare-fun bhr37_22667 () Int)
(declare-fun n () Int)
(declare-fun nl37_22661 () Int)
(declare-fun nr37_22665 () Int)
(declare-fun cl () Int)
(declare-fun flted289_22658 () Int)


(assert 
(exists ((flted289 Int)(v57 Int)(l37 node)(nl37 Int)(Anon25 Int)(bhl37 Int)(r37 node)(nr37 Int)(Anon26 Int)(bhr37 Int))(and 
;lexvar(= xprm x)
(= aprm a)
(<= 0 cl)
(<= cl 1)
(distinct xprm nil)
(= bh (+ bhl37 1))
(= bhl37 bhr37)
(= n (+ (+ nr37 1) nl37))
(= cl 0)
(= flted289 0)
(tobool (ssep 
(pto xprm (sref (ref val v57) (ref color flted289) (ref left l37) (ref right r37) ))
(rb l37 nl37 Anon25 bhl37)
(rb r37 nr37 Anon26 bhr37)
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