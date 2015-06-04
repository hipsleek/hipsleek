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





































































































































































































































































































































































(declare-fun v16_5176 () Int)
(declare-fun l8_5177 () node)
(declare-fun r8_5180 () node)
(declare-fun x () node)
(declare-fun xprm () node)
(declare-fun bhr8_5182 () Int)
(declare-fun bhl8_5179 () Int)
(declare-fun bh () Int)
(declare-fun n () Int)
(declare-fun nl8_5178 () Int)
(declare-fun nr8_5181 () Int)
(declare-fun cl () Int)
(declare-fun flted104_5173 () Int)
(declare-fun flted105_5174 () Int)
(declare-fun flted106_5175 () Int)


(assert 
(exists ((flted104 Int)(flted105 Int)(flted106 Int)(v16 Int)(l8 node)(nl8 Int)(bhl8 Int)(r8 node)(nr8 Int)(bhr8 Int))(and 
;lexvar(= xprm x)
(distinct xprm nil)
(= bhr8 bh)
(= bhl8 bh)
(= n (+ (+ nr8 1) nl8))
(= cl 1)
(= flted104 0)
(= flted105 0)
(= flted106 1)
(tobool (ssep 
(pto xprm (sref (ref val v16) (ref color flted106) (ref left l8) (ref right r8) ))
(rb l8 nl8 flted105 bhl8)
(rb r8 nr8 flted104 bhr8)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val1prm) (ref color color2prm) (ref left left1prm) (ref right right1prm) ))
 )
)
))

(check-sat)