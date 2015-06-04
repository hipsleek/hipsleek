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





































































































































































































































































































































































(declare-fun tmp_749 () node)
(declare-fun v8prm () node)
(declare-fun v12_748 () Int)
(declare-fun v11_747 () Int)
(declare-fun v10_746 () Int)
(declare-fun v9_745 () Int)
(declare-fun flted20_742 () Int)
(declare-fun flted21_743 () Int)
(declare-fun flted22_744 () Int)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bha_750 () Int)
(declare-fun bha_751 () Int)
(declare-fun res () node)
(declare-fun nc () Int)
(declare-fun nb () Int)
(declare-fun bha () Int)
(declare-fun na () Int)


(assert 
(exists ((flted20 Int)(flted21 Int)(flted22 Int)(v9prm Int)(v10prm Int)(v11prm Int)(v12prm Int)(tmpprm node))(and 
;lexvar(= res v8prm)
(= v12prm 0)
(= v11prm 0)
(= v10prm 1)
(= v9prm 0)
(= flted20 1)
(= flted21 0)
(= flted22 0)
(= cprm c)
(= bprm b)
(= aprm a)
(tobool (ssep 
(rb a na flted22 bha)
(rb b nb flted21 bha)
(rb c nc flted20 bha)
(pto tmpprm (sref (ref val v9prm) (ref color v10prm) (ref left aprm) (ref right bprm) ))
(pto v8prm (sref (ref val v11prm) (ref color v12prm) (ref left tmpprm) (ref right cprm) ))
) )
))
)

(assert (not 
(exists ((flted23 Int)(flted24 Int)(flted25 Int))(and 
(= flted23 (+ 1 bha))
(= flted24 0)
(= flted25 (+ (+ (+ 2 nb) na) nc))
(<= 0 nc)
(<= 0 nb)
(<= 1 bha)
(<= 0 na)
(tobool  
(rb res flted25 flted24 flted23)
 )
))
))

(check-sat)