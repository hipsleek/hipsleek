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





































































































































































































































































































































































(declare-fun Anon32 () Int)
(declare-fun l45 () node)
(declare-fun r45 () node)
(declare-fun Anon33 () Int)
(declare-fun flted340 () Int)
(declare-fun Anon29 () Int)
(declare-fun n () Int)
(declare-fun nl45 () Int)
(declare-fun nr45 () Int)
(declare-fun bhr45 () Int)
(declare-fun bh () Int)
(declare-fun bhl45 () Int)
(declare-fun tmp1prm () node)
(declare-fun v90 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun v94 () Int)
(declare-fun v127prm () Int)
(declare-fun v125prm () Int)


(assert 
(and 
;lexvar(= flted340 0)
(= Anon29 0)
(= n (+ (+ nr45 1) nl45))
(= bhl45 bhr45)
(= bh (+ bhl45 1))
(distinct xprm nil)
(= tmp1prm nil)
(= v125prm v90)
(= xprm x)
(= v127prm v94)
(< v127prm v125prm)
(tobool (ssep 
(rb l45 nl45 Anon32 bhl45)
(pto xprm (sref (ref val v94) (ref color flted340) (ref left l45) (ref right r45) ))
(rb r45 nr45 Anon33 bhr45)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)