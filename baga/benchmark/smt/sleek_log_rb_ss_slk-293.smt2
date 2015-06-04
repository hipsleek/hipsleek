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





































































































































































































































































































































































(declare-fun v92_29139 () Int)
(declare-fun l43_29140 () node)
(declare-fun Anon30_29142 () Int)
(declare-fun r43_29144 () node)
(declare-fun Anon31_29146 () Int)
(declare-fun x () node)
(declare-fun v125prm () node)
(declare-fun v90 () node)
(declare-fun tmp1prm () node)
(declare-fun xprm () node)
(declare-fun bh () Int)
(declare-fun bhl43_29143 () Int)
(declare-fun bhr43_29147 () Int)
(declare-fun n () Int)
(declare-fun nl43_29141 () Int)
(declare-fun nr43_29145 () Int)
(declare-fun Anon29 () Int)
(declare-fun flted336_29138 () Int)


(assert 
(exists ((flted336 Int)(v92 Int)(l43 node)(nl43 Int)(Anon30 Int)(bhl43 Int)(r43 node)(nr43 Int)(Anon31 Int)(bhr43 Int))(and 
;lexvar(= xprm x)
(= v125prm v90)
(= tmp1prm nil)
(distinct xprm nil)
(= bh (+ bhl43 1))
(= bhl43 bhr43)
(= n (+ (+ nr43 1) nl43))
(= Anon29 0)
(= flted336 0)
(tobool (ssep 
(pto xprm (sref (ref val v92) (ref color flted336) (ref left l43) (ref right r43) ))
(rb l43 nl43 Anon30 bhl43)
(rb r43 nr43 Anon31 bhr43)
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