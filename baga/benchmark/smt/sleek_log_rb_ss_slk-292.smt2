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





































































































































































































































































































































































(declare-fun v91_29087 () Int)
(declare-fun l42_29088 () node)
(declare-fun r42_29091 () node)
(declare-fun x () node)
(declare-fun v125prm () node)
(declare-fun v90 () node)
(declare-fun tmp1prm () node)
(declare-fun xprm () node)
(declare-fun bhr42_29093 () Int)
(declare-fun bhl42_29090 () Int)
(declare-fun bh () Int)
(declare-fun n () Int)
(declare-fun nl42_29089 () Int)
(declare-fun nr42_29092 () Int)
(declare-fun Anon29 () Int)
(declare-fun flted333_29084 () Int)
(declare-fun flted334_29085 () Int)
(declare-fun flted335_29086 () Int)


(assert 
(exists ((flted333 Int)(flted334 Int)(flted335 Int)(v91 Int)(l42 node)(nl42 Int)(bhl42 Int)(r42 node)(nr42 Int)(bhr42 Int))(and 
;lexvar(= xprm x)
(= v125prm v90)
(= tmp1prm nil)
(distinct xprm nil)
(= bhr42 bh)
(= bhl42 bh)
(= n (+ (+ nr42 1) nl42))
(= Anon29 1)
(= flted333 0)
(= flted334 0)
(= flted335 1)
(tobool (ssep 
(pto xprm (sref (ref val v91) (ref color flted335) (ref left l42) (ref right r42) ))
(rb l42 nl42 flted334 bhl42)
(rb r42 nr42 flted333 bhr42)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val47prm) (ref color color48prm) (ref left left47prm) (ref right right47prm) ))
 )
)
))

(check-sat)