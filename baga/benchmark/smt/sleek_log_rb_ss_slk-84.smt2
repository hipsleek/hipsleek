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





































































































































































































































































































































































(declare-fun bhr21 () Int)
(declare-fun nr21 () Int)
(declare-fun bhl21 () Int)
(declare-fun nl21 () Int)
(declare-fun r21 () node)
(declare-fun l21 () node)
(declare-fun v32 () Int)
(declare-fun v31 () Int)
(declare-fun v33 () Int)
(declare-fun dprm () node)
(declare-fun d () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun flted193 () Int)
(declare-fun flted192 () Int)
(declare-fun flted191 () Int)
(declare-fun flted190 () Int)
(declare-fun tmp_13103 () node)
(declare-fun flted205_13102 () Int)
(declare-fun flted204_13101 () Int)
(declare-fun flted203_13100 () Int)
(declare-fun colorprm () Int)
(declare-fun Anon10 () Int)
(declare-fun na7 () Int)
(declare-fun ha () Int)
(declare-fun nb7 () Int)
(declare-fun Anon11 () Int)
(declare-fun nc7 () Int)
(declare-fun v65prm () node)
(declare-fun res () node)
(declare-fun color () Int)
(declare-fun na () Int)
(declare-fun h () Int)
(declare-fun nb () Int)
(declare-fun nc () Int)
(declare-fun nd () Int)


(assert 
(exists ((flted203 Int)(flted204 Int)(flted205 Int)(tmpprm Int))(and 
;lexvar(= na7 (+ (+ nr21 1) nl21))
(= bhl21 ha)
(= bhr21 ha)
(= bhr21 bhl21)
(= bhr21 h)
(= nr21 nb)
(= bhl21 h)
(= nl21 na)
(= r21 bprm)
(= l21 aprm)
(= v32 v33)
(= v31 1)
(= v33 0)
(= color 1)
(= flted193 0)
(= flted192 0)
(= flted191 0)
(= flted190 0)
(= colorprm color)
(= dprm d)
(= cprm c)
(= bprm b)
(= aprm a)
(= nb7 nc)
(= Anon11 flted192)
(= nc7 nd)
(<= 0 nd)
(<= 0 flted193)
(<= flted193 1)
(<= 0 nc)
(<= 0 flted192)
(<= flted192 1)
(<= 0 nb)
(<= 0 flted191)
(<= flted191 1)
(<= 0 na)
(<= 1 h)
(<= 0 flted190)
(<= flted190 1)
(distinct tmpprm nil)
(= flted205 (+ (+ (+ 2 nb7) na7) nc7))
(= flted204 1)
(= flted203 (+ 1 ha))
(= colorprm 1)
(= res v65prm)
(tobool  
(rb v65prm flted205 flted204 flted203)
 )
))
)

(assert (not 
(exists ((flted200 Int)(flted201 Int)(flted202 Int))(and 
(= color 1)
(= flted200 (+ 1 h))
(= flted201 1)
(= flted202 (+ (+ (+ (+ 3 nc) na) nb) nd))
(tobool  
(rb res flted202 flted201 flted200)
 )
))
))

(check-sat)