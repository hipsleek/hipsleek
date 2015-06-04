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





































































































































































































































































































































































(declare-fun bhr1 () Int)
(declare-fun nr1 () Int)
(declare-fun bhl1 () Int)
(declare-fun nl1 () Int)
(declare-fun r1 () node)
(declare-fun l1 () node)
(declare-fun v4 () Int)
(declare-fun v3 () Int)
(declare-fun v5 () Int)
(declare-fun dprm () node)
(declare-fun d () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun flted33 () Int)
(declare-fun flted32 () Int)
(declare-fun tmp_1136 () node)
(declare-fun flted31 () Int)
(declare-fun flted30 () Int)
(declare-fun flted36_1135 () Int)
(declare-fun flted35_1134 () Int)
(declare-fun flted34_1133 () Int)
(declare-fun na2 () Int)
(declare-fun bha4 () Int)
(declare-fun nb2 () Int)
(declare-fun nc2 () Int)
(declare-fun v15prm () node)
(declare-fun res () node)
(declare-fun nd () Int)
(declare-fun nc () Int)
(declare-fun nb () Int)
(declare-fun bha () Int)
(declare-fun na () Int)


(assert 
(exists ((flted34 Int)(flted35 Int)(flted36 Int)(tmpprm Int))(and 
;lexvar(= nc2 (+ (+ nr1 1) nl1))
(= bhr1 bha)
(= nr1 nd)
(= bhl1 bha)
(= nl1 nc)
(= r1 dprm)
(= l1 cprm)
(= v4 v5)
(= v3 1)
(= v5 0)
(= flted33 0)
(= flted32 0)
(= flted31 0)
(= flted30 0)
(= dprm d)
(= cprm c)
(= bprm b)
(= aprm a)
(= na2 na)
(= bha4 bha)
(= nb2 nb)
(<= 0 nd)
(<= 0 flted33)
(<= flted33 1)
(<= 0 nc)
(<= 0 flted32)
(<= flted32 1)
(distinct tmpprm nil)
(<= 0 nb)
(<= 0 flted31)
(<= flted31 1)
(<= 0 na)
(<= 1 bha)
(<= 0 flted30)
(<= flted30 1)
(= flted36 (+ (+ (+ 2 nb2) na2) nc2))
(= flted35 0)
(= flted34 (+ 1 bha4))
(<= 0 na2)
(<= 1 bha4)
(<= 0 nb2)
(<= 0 nc2)
(= res v15prm)
(tobool  
(rb v15prm flted36 flted35 flted34)
 )
))
)

(assert (not 
(exists ((flted37 Int)(flted38 Int)(flted39 Int))(and 
(= flted37 (+ 1 bha))
(= flted38 0)
(= flted39 (+ (+ (+ (+ 3 nc) na) nb) nd))
(<= 0 nd)
(<= 0 nc)
(<= 0 nb)
(<= 1 bha)
(<= 0 na)
(tobool  
(rb res flted39 flted38 flted37)
 )
))
))

(check-sat)