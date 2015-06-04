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





































































































































































































































































































































































(declare-fun v9 () Int)
(declare-fun l5 () node)
(declare-fun r5 () node)
(declare-fun tmp_2789 () node)
(declare-fun v21prm () node)
(declare-fun v24_2788 () Int)
(declare-fun v23_2787 () Int)
(declare-fun v22_2786 () Int)
(declare-fun color2 () Int)
(declare-fun flted67 () Int)
(declare-fun flted68 () Int)
(declare-fun flted69 () Int)
(declare-fun flted70 () Int)
(declare-fun nl5 () Int)
(declare-fun nr5 () Int)
(declare-fun bhl5 () Int)
(declare-fun bhr5 () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun colorprm () Int)
(declare-fun flted71 () Int)
(declare-fun h7 () Int)
(declare-fun h8 () Int)
(declare-fun v20_2785 () Int)
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
(= color2 flted67)
(= flted67 1)
(= flted68 0)
(= flted69 0)
(= flted70 1)
(= nc (+ (+ nr5 1) nl5))
(= bhl5 h8)
(= bhr5 h8)
(= aprm a)
(= bprm b)
(= cprm c)
(= colorprm color)
(= flted71 0)
(= color 1)
(= h7 h)
(= h8 h)
(= v20prm 0)
(tobool (ssep 
(rb a na flted71 h)
(rb b nb Anon1 h7)
(rb l5 nl5 flted68 bhl5)
(rb r5 nr5 flted69 bhr5)
(pto cprm (sref (ref val v9) (ref color v20prm) (ref left l5) (ref right r5) ))
(pto tmpprm (sref (ref val v22prm) (ref color v23prm) (ref left aprm) (ref right bprm) ))
(pto v21prm (sref (ref val v24prm) (ref color colorprm) (ref left tmpprm) (ref right cprm) ))
) )
))
)

(assert (not 
(exists ((flted64 Int)(flted65 Int)(flted66 Int))(and 
(= color 1)
(= flted64 (+ 1 h))
(= flted65 1)
(= flted66 (+ (+ (+ 2 nb) na) nc))
(tobool  
(rb res flted66 flted65 flted64)
 )
))
))

(check-sat)