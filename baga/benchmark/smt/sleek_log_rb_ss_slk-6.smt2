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





































































































































































































































































































































































(declare-fun bhr () Int)
(declare-fun nr () Int)
(declare-fun bhl () Int)
(declare-fun nl () Int)
(declare-fun r () node)
(declare-fun l () node)
(declare-fun v1 () Int)
(declare-fun v () Int)
(declare-fun v2 () Int)
(declare-fun dprm () node)
(declare-fun d () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun flted13 () Int)
(declare-fun flted12 () Int)
(declare-fun flted11 () Int)
(declare-fun flted10 () Int)
(declare-fun tmp_549 () node)
(declare-fun flted16_548 () Int)
(declare-fun flted15_547 () Int)
(declare-fun flted14_546 () Int)
(declare-fun na1 () Int)
(declare-fun bha1 () Int)
(declare-fun nb1 () Int)
(declare-fun nc1 () Int)
(declare-fun v7prm () node)
(declare-fun res () node)
(declare-fun nd () Int)
(declare-fun nc () Int)
(declare-fun nb () Int)
(declare-fun bha () Int)
(declare-fun na () Int)


(assert 
(exists ((flted14 Int)(flted15 Int)(flted16 Int)(tmpprm Int))(and 
;lexvar(= na1 (+ (+ nr 1) nl))
(= bhl bha1)
(= bhr bha1)
(= bhr bhl)
(= bhr bha)
(= nr nb)
(= bhl bha)
(= nl na)
(= r bprm)
(= l aprm)
(= v1 v2)
(= v 1)
(= v2 0)
(= flted13 0)
(= flted12 0)
(= flted11 0)
(= flted10 0)
(= dprm d)
(= cprm c)
(= bprm b)
(= aprm a)
(= nb1 nc)
(= nc1 nd)
(<= 0 nd)
(<= 0 flted13)
(<= flted13 1)
(<= 0 nc)
(<= 0 flted12)
(<= flted12 1)
(<= 0 nb)
(<= 0 flted11)
(<= flted11 1)
(<= 0 na)
(<= 1 bha)
(<= 0 flted10)
(<= flted10 1)
(distinct tmpprm nil)
(= flted16 (+ (+ (+ 2 nb1) na1) nc1))
(= flted15 0)
(= flted14 (+ 1 bha1))
(<= 0 na1)
(<= 1 bha1)
(<= 0 nb1)
(<= 0 nc1)
(= res v7prm)
(tobool  
(rb v7prm flted16 flted15 flted14)
 )
))
)

(assert (not 
(exists ((flted17 Int)(flted18 Int)(flted19 Int))(and 
(= flted17 (+ 1 bha))
(= flted18 0)
(= flted19 (+ (+ (+ (+ 3 nc) na) nb) nd))
(<= 0 nd)
(<= 0 nc)
(<= 0 nb)
(<= 1 bha)
(<= 0 na)
(tobool  
(rb res flted19 flted18 flted17)
 )
))
))

(check-sat)