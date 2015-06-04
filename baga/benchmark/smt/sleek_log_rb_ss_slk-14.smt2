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





































































































































































































































































































































































(declare-fun v8 () Int)
(declare-fun l4 () node)
(declare-fun r4 () node)
(declare-fun tmp_1695 () node)
(declare-fun v21prm () node)
(declare-fun v24_1694 () Int)
(declare-fun v23_1693 () Int)
(declare-fun v22_1692 () Int)
(declare-fun color1 () Int)
(declare-fun flted56 () Int)
(declare-fun flted57 () Int)
(declare-fun flted58 () Int)
(declare-fun flted59 () Int)
(declare-fun nl4 () Int)
(declare-fun nr4 () Int)
(declare-fun bhl4 () Int)
(declare-fun bhr4 () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun colorprm () Int)
(declare-fun flted60 () Int)
(declare-fun h5 () Int)
(declare-fun h6 () Int)
(declare-fun v20_1691 () Int)
(declare-fun res () node)
(declare-fun color () Int)
(declare-fun Anon () Int)
(declare-fun na () Int)
(declare-fun h () Int)
(declare-fun nb () Int)
(declare-fun Anon1 () Int)
(declare-fun nc () Int)


(assert 
(exists ((v20prm Int)(v22prm Int)(v23prm Int)(v24prm Int)(tmpprm node))(and 
;lexvar(= res v21prm)
(= v24prm 0)
(= v23prm 0)
(= v22prm 0)
(= color1 flted56)
(= flted56 1)
(= flted57 0)
(= flted58 0)
(= flted59 1)
(= nc (+ (+ nr4 1) nl4))
(= bhl4 h6)
(= bhr4 h6)
(= aprm a)
(= bprm b)
(= cprm c)
(= colorprm color)
(= flted60 0)
(= color 0)
(= h5 h)
(= h6 h)
(= v20prm 0)
(tobool (ssep 
(rb a na flted60 h)
(rb b nb Anon h5)
(rb l4 nl4 flted57 bhl4)
(rb r4 nr4 flted58 bhr4)
(pto cprm (sref (ref val v8) (ref color v20prm) (ref left l4) (ref right r4) ))
(pto tmpprm (sref (ref val v22prm) (ref color v23prm) (ref left aprm) (ref right bprm) ))
(pto v21prm (sref (ref val v24prm) (ref color colorprm) (ref left tmpprm) (ref right cprm) ))
) )
))
)

(assert (not 
(exists ((flted61 Int)(flted62 Int)(flted63 Int))(and 
(= color 0)
(= flted61 (+ 2 h))
(= flted62 0)
(= flted63 (+ (+ (+ 2 nb) na) nc))
(tobool  
(rb res flted63 flted62 flted61)
 )
))
))

(check-sat)