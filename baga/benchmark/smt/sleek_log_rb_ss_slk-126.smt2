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





































































































































































































































































































































































(declare-fun v38_19175 () Int)
(declare-fun l26_19176 () node)
(declare-fun r26_19179 () node)
(declare-fun x () node)
(declare-fun xprm () node)
(declare-fun bhr26_19181 () Int)
(declare-fun bhl26_19178 () Int)
(declare-fun bh () Int)
(declare-fun n () Int)
(declare-fun nl26_19177 () Int)
(declare-fun nr26_19180 () Int)
(declare-fun cl () Int)
(declare-fun flted251_19172 () Int)
(declare-fun flted252_19173 () Int)
(declare-fun flted253_19174 () Int)


(assert 
(exists ((flted251 Int)(flted252 Int)(flted253 Int)(v38 Int)(l26 node)(nl26 Int)(bhl26 Int)(r26 node)(nr26 Int)(bhr26 Int))(and 
;lexvar(= xprm x)
(distinct xprm nil)
(= bhr26 bh)
(= bhl26 bh)
(= n (+ (+ nr26 1) nl26))
(= cl 1)
(= flted251 0)
(= flted252 0)
(= flted253 1)
(tobool (ssep 
(pto xprm (sref (ref val v38) (ref color flted253) (ref left l26) (ref right r26) ))
(rb l26 nl26 flted252 bhl26)
(rb r26 nr26 flted251 bhr26)
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