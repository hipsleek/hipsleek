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





































































































































































































































































































































































(declare-fun v39_19222 () Int)
(declare-fun l27_19223 () node)
(declare-fun Anon17_19225 () Int)
(declare-fun r27_19227 () node)
(declare-fun Anon18_19229 () Int)
(declare-fun x () node)
(declare-fun xprm () node)
(declare-fun bh () Int)
(declare-fun bhl27_19226 () Int)
(declare-fun bhr27_19230 () Int)
(declare-fun n () Int)
(declare-fun nl27_19224 () Int)
(declare-fun nr27_19228 () Int)
(declare-fun cl () Int)
(declare-fun flted254_19221 () Int)


(assert 
(exists ((flted254 Int)(v39 Int)(l27 node)(nl27 Int)(Anon17 Int)(bhl27 Int)(r27 node)(nr27 Int)(Anon18 Int)(bhr27 Int))(and 
;lexvar(= xprm x)
(distinct xprm nil)
(= bh (+ bhl27 1))
(= bhl27 bhr27)
(= n (+ (+ nr27 1) nl27))
(= cl 0)
(= flted254 0)
(tobool (ssep 
(pto xprm (sref (ref val v39) (ref color flted254) (ref left l27) (ref right r27) ))
(rb l27 nl27 Anon17 bhl27)
(rb r27 nr27 Anon18 bhr27)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val25prm) (ref color color26prm) (ref left left25prm) (ref right right25prm) ))
 )
)
))

(check-sat)