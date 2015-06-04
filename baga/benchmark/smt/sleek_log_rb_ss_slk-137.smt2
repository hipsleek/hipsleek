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





































































































































































































































































































































































(declare-fun v43_19836 () Int)
(declare-fun l31_19837 () node)
(declare-fun Anon21_19839 () Int)
(declare-fun r31_19841 () node)
(declare-fun Anon22_19843 () Int)
(declare-fun flted262_19835 () Int)
(declare-fun n () Int)
(declare-fun nl31_19838 () Int)
(declare-fun nr31_19842 () Int)
(declare-fun bhr31_19844 () Int)
(declare-fun bh () Int)
(declare-fun bhl31_19840 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun cl () Int)


(assert 
(exists ((flted262 Int)(v43 Int)(l31 node)(nl31 Int)(Anon21 Int)(bhl31 Int)(r31 node)(nr31 Int)(Anon22 Int)(bhr31 Int))(and 
;lexvar(= flted262 0)
(= cl 0)
(= n (+ (+ nr31 1) nl31))
(= bhl31 bhr31)
(= bh (+ bhl31 1))
(= xprm x)
(distinct x nil)
(<= 0 cl)
(<= cl 1)
(tobool (ssep 
(pto xprm (sref (ref val v43) (ref color flted262) (ref left l31) (ref right r31) ))
(rb l31 nl31 Anon21 bhl31)
(rb r31 nr31 Anon22 bhr31)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val26prm) (ref color color27prm) (ref left left26prm) (ref right right26prm) ))
 )
)
))

(check-sat)