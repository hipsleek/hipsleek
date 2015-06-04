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





































































































































































































































































































































































(declare-fun bhr6 () Int)
(declare-fun nr6 () Int)
(declare-fun bhl6 () Int)
(declare-fun nl6 () Int)
(declare-fun r6 () node)
(declare-fun l6 () node)
(declare-fun v11 () Int)
(declare-fun v10 () Int)
(declare-fun v12 () Int)
(declare-fun dprm () node)
(declare-fun d () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun flted83 () Int)
(declare-fun flted82 () Int)
(declare-fun tmp_4028 () node)
(declare-fun flted81 () Int)
(declare-fun flted80 () Int)
(declare-fun flted94_4027 () Int)
(declare-fun flted93_4026 () Int)
(declare-fun flted92_4025 () Int)
(declare-fun colorprm () Int)
(declare-fun Anon () Int)
(declare-fun na3 () Int)
(declare-fun h9 () Int)
(declare-fun nb3 () Int)
(declare-fun Anon1 () Int)
(declare-fun nc3 () Int)
(declare-fun v27prm () node)
(declare-fun res () node)
(declare-fun color () Int)
(declare-fun na () Int)
(declare-fun h () Int)
(declare-fun nb () Int)
(declare-fun nc () Int)
(declare-fun nd () Int)


(assert 
(exists ((flted92 Int)(flted93 Int)(flted94 Int)(tmpprm Int))(and 
;lexvar(= nc3 (+ (+ nr6 1) nl6))
(= bhr6 h)
(= nr6 nd)
(= bhl6 h)
(= nl6 nc)
(= r6 dprm)
(= l6 cprm)
(= v11 v12)
(= v10 1)
(= v12 0)
(= color 0)
(= flted83 0)
(= flted82 0)
(= flted81 0)
(= flted80 0)
(= colorprm color)
(= dprm d)
(= cprm c)
(= bprm b)
(= aprm a)
(= na3 na)
(= h9 h)
(= nb3 nb)
(= Anon flted81)
(<= 0 nd)
(<= 0 flted83)
(<= flted83 1)
(<= 0 nc)
(<= 0 flted82)
(<= flted82 1)
(distinct tmpprm nil)
(<= 0 nb)
(<= 0 flted81)
(<= flted81 1)
(<= 0 na)
(<= 1 h)
(<= 0 flted80)
(<= flted80 1)
(= flted94 (+ (+ (+ 2 nb3) na3) nc3))
(= flted93 0)
(= flted92 (+ 2 h9))
(= colorprm 0)
(= res v27prm)
(tobool  
(rb v27prm flted94 flted93 flted92)
 )
))
)

(assert (not 
(exists ((flted95 Int)(flted96 Int)(flted97 Int))(and 
(= color 0)
(= flted95 (+ 2 h))
(= flted96 0)
(= flted97 (+ (+ (+ (+ 3 nc) na) nb) nd))
(tobool  
(rb res flted97 flted96 flted95)
 )
))
))

(check-sat)