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
(declare-fun v34_13362 () Int)
(declare-fun l22_13363 () node)
(declare-fun Anon12_13365 () Int)
(declare-fun r22_13367 () node)
(declare-fun Anon13_13369 () Int)
(declare-fun nc () Int)
(declare-fun flted206_13361 () Int)
(declare-fun flted209_13373 () Int)
(declare-fun nb () Int)
(declare-fun nl22_13364 () Int)
(declare-fun nr22_13368 () Int)
(declare-fun bhr22_13370 () Int)
(declare-fun bhl22_13366 () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun flted211_13375 () Int)
(declare-fun flted210_13374 () Int)
(declare-fun flted208_13372 () Int)
(declare-fun h () Int)
(declare-fun flted207_13371 () Int)
(declare-fun b () node)


(assert 
(exists ((flted206 Int)(v34 Int)(l22 node)(nl22 Int)(Anon12 Int)(bhl22 Int)(r22 node)(nr22 Int)(Anon13 Int)(bhr22 Int)(flted207 Int)(flted208 Int)(flted209 Int)(flted210 Int)(flted211 Int))(and 
;lexvar(= flted206 0)
(= flted209 0)
(= nb (+ (+ nr22 1) nl22))
(= bhl22 bhr22)
(= flted208 (+ bhl22 1))
(= aprm a)
(= bprm b)
(= cprm c)
(= flted211 0)
(= flted210 (+ 1 h))
(= flted208 (+ 1 h))
(= flted207 0)
(distinct b nil)
(tobool (ssep 
(rb a na flted211 flted210)
(pto bprm (sref (ref val v34) (ref color flted206) (ref left l22) (ref right r22) ))
(rb l22 nl22 Anon12 bhl22)
(rb r22 nr22 Anon13 bhr22)
(rb c nc flted207 h)
) )
))
)

(assert (not 
(and 
(tobool  
(pto bprm (sref (ref val val14prm) (ref color color15prm) (ref left left14prm) (ref right right14prm) ))
 )
)
))

(check-sat)