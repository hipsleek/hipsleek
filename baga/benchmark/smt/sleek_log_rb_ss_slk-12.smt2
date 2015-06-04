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





































































































































































































































































































































































(declare-fun na () Int)
(declare-fun nb () Int)
(declare-fun Anon () Int)
(declare-fun v6_1550 () Int)
(declare-fun l2_1551 () node)
(declare-fun r2_1554 () node)
(declare-fun flted48_1549 () Int)
(declare-fun flted47_1548 () Int)
(declare-fun flted46_1547 () Int)
(declare-fun flted49_1559 () Int)
(declare-fun nc () Int)
(declare-fun nl2_1552 () Int)
(declare-fun nr2_1555 () Int)
(declare-fun bhl2_1553 () Int)
(declare-fun bhr2_1556 () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun colorprm () Int)
(declare-fun flted50_1560 () Int)
(declare-fun color () Int)
(declare-fun h1_1557 () Int)
(declare-fun h2_1558 () Int)
(declare-fun h () Int)
(declare-fun v20prm () Int)


(assert 
(exists ((flted46 Int)(flted47 Int)(flted48 Int)(v6 Int)(l2 node)(nl2 Int)(bhl2 Int)(r2 node)(nr2 Int)(bhr2 Int)(h1 Int)(h2 Int)(flted49 Int)(flted50 Int))(and 
;lexvar(= flted48 1)
(= flted47 0)
(= flted46 0)
(= flted49 1)
(= nc (+ (+ nr2 1) nl2))
(= bhl2 h2)
(= bhr2 h2)
(= aprm a)
(= bprm b)
(= cprm c)
(= colorprm color)
(= flted50 0)
(= color 0)
(= h1 h)
(= h2 h)
(= v20prm 0)
(tobool (ssep 
(rb a na flted50 h)
(rb b nb Anon h1)
(pto cprm (sref (ref val v6) (ref color flted48) (ref left l2) (ref right r2) ))
(rb l2 nl2 flted47 bhl2)
(rb r2 nr2 flted46 bhr2)
) )
))
)

(assert (not 
(and 
(tobool  
(pto cprm (sref (ref val valprm) (ref color color1prm) (ref left leftprm) (ref right rightprm) ))
 )
)
))

(check-sat)