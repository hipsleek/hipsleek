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





































































































































































































































































































































































(declare-fun bhr7 () Int)
(declare-fun nr7 () Int)
(declare-fun bhl7 () Int)
(declare-fun nl7 () Int)
(declare-fun r7 () node)
(declare-fun l7 () node)
(declare-fun v14 () Int)
(declare-fun v13 () Int)
(declare-fun v15 () Int)
(declare-fun dprm () node)
(declare-fun d () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun flted91 () Int)
(declare-fun flted90 () Int)
(declare-fun tmp_4874 () node)
(declare-fun flted89 () Int)
(declare-fun flted88 () Int)
(declare-fun flted103_4873 () Int)
(declare-fun flted102_4872 () Int)
(declare-fun flted101_4871 () Int)
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
(exists ((flted101 Int)(flted102 Int)(flted103 Int)(tmpprm Int))(and 
;lexvar(= nc3 (+ (+ nr7 1) nl7))
(= bhr7 h)
(= nr7 nd)
(= bhl7 h)
(= nl7 nc)
(= r7 dprm)
(= l7 cprm)
(= v14 v15)
(= v13 1)
(= v15 0)
(= color 1)
(= flted91 0)
(= flted90 0)
(= flted89 0)
(= flted88 0)
(= colorprm color)
(= dprm d)
(= cprm c)
(= bprm b)
(= aprm a)
(= na3 na)
(= h9 h)
(= nb3 nb)
(= Anon1 flted89)
(<= 0 nd)
(<= 0 flted91)
(<= flted91 1)
(<= 0 nc)
(<= 0 flted90)
(<= flted90 1)
(distinct tmpprm nil)
(<= 0 nb)
(<= 0 flted89)
(<= flted89 1)
(<= 0 na)
(<= 1 h)
(<= 0 flted88)
(<= flted88 1)
(= flted103 (+ (+ (+ 2 nb3) na3) nc3))
(= flted102 1)
(= flted101 (+ 1 h9))
(= colorprm 1)
(= res v27prm)
(tobool  
(rb v27prm flted103 flted102 flted101)
 )
))
)

(assert (not 
(exists ((flted98 Int)(flted99 Int)(flted100 Int))(and 
(= color 1)
(= flted98 (+ 1 h))
(= flted99 1)
(= flted100 (+ (+ (+ (+ 3 nc) na) nb) nd))
(tobool  
(rb res flted100 flted99 flted98)
 )
))
))

(check-sat)