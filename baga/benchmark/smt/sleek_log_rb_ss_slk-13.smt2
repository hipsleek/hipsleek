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
(declare-fun Anon1 () Int)
(declare-fun v7_1622 () Int)
(declare-fun l3_1623 () node)
(declare-fun r3_1626 () node)
(declare-fun flted53_1621 () Int)
(declare-fun flted52_1620 () Int)
(declare-fun flted51_1619 () Int)
(declare-fun flted54_1631 () Int)
(declare-fun nc () Int)
(declare-fun nl3_1624 () Int)
(declare-fun nr3_1627 () Int)
(declare-fun bhl3_1625 () Int)
(declare-fun bhr3_1628 () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun colorprm () Int)
(declare-fun flted55_1632 () Int)
(declare-fun color () Int)
(declare-fun h3_1629 () Int)
(declare-fun h4_1630 () Int)
(declare-fun h () Int)
(declare-fun v20prm () Int)


(assert 
(exists ((flted51 Int)(flted52 Int)(flted53 Int)(v7 Int)(l3 node)(nl3 Int)(bhl3 Int)(r3 node)(nr3 Int)(bhr3 Int)(h3 Int)(h4 Int)(flted54 Int)(flted55 Int))(and 
;lexvar(= flted53 1)
(= flted52 0)
(= flted51 0)
(= flted54 1)
(= nc (+ (+ nr3 1) nl3))
(= bhl3 h4)
(= bhr3 h4)
(= aprm a)
(= bprm b)
(= cprm c)
(= colorprm color)
(= flted55 0)
(= color 1)
(= h3 h)
(= h4 h)
(= v20prm 0)
(tobool (ssep 
(rb a na flted55 h)
(rb b nb Anon1 h3)
(pto cprm (sref (ref val v7) (ref color flted53) (ref left l3) (ref right r3) ))
(rb l3 nl3 flted52 bhl3)
(rb r3 nr3 flted51 bhr3)
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