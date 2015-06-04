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





































































































































































































































































































































































(declare-fun v42_19788 () Int)
(declare-fun l30_19789 () node)
(declare-fun r30_19792 () node)
(declare-fun flted261_19787 () Int)
(declare-fun flted260_19786 () Int)
(declare-fun flted259_19785 () Int)
(declare-fun n () Int)
(declare-fun nl30_19790 () Int)
(declare-fun nr30_19793 () Int)
(declare-fun bhl30_19791 () Int)
(declare-fun bhr30_19794 () Int)
(declare-fun bh () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun cl () Int)


(assert 
(exists ((flted259 Int)(flted260 Int)(flted261 Int)(v42 Int)(l30 node)(nl30 Int)(bhl30 Int)(r30 node)(nr30 Int)(bhr30 Int))(and 
;lexvar(= flted261 1)
(= flted260 0)
(= flted259 0)
(= cl 1)
(= n (+ (+ nr30 1) nl30))
(= bhl30 bh)
(= bhr30 bh)
(= xprm x)
(distinct x nil)
(<= 0 cl)
(<= cl 1)
(tobool (ssep 
(pto xprm (sref (ref val v42) (ref color flted261) (ref left l30) (ref right r30) ))
(rb l30 nl30 flted260 bhl30)
(rb r30 nr30 flted259 bhr30)
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