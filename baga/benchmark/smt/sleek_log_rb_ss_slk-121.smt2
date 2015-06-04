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





































































































































































































































































































































































(declare-fun tmp_18920 () node)
(declare-fun v88prm () node)
(declare-fun v92_18919 () Int)
(declare-fun v91_18918 () Int)
(declare-fun v90_18917 () Int)
(declare-fun v89_18916 () Int)
(declare-fun flted245_18913 () Int)
(declare-fun flted246_18914 () Int)
(declare-fun flted247_18915 () Int)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun ha_18921 () Int)
(declare-fun ha_18922 () Int)
(declare-fun res () node)
(declare-fun nc () Int)
(declare-fun nb () Int)
(declare-fun ha () Int)
(declare-fun na () Int)


(assert 
(exists ((flted245 Int)(flted246 Int)(flted247 Int)(v89prm Int)(v90prm Int)(v91prm Int)(v92prm Int)(tmpprm node))(and 
;lexvar(= res v88prm)
(= v92prm 0)
(= v91prm 0)
(= v90prm 1)
(= v89prm 0)
(= flted245 0)
(= flted246 0)
(= flted247 0)
(= cprm c)
(= bprm b)
(= aprm a)
(tobool (ssep 
(rb a na flted247 ha)
(rb b nb flted246 ha)
(rb c nc flted245 ha)
(pto tmpprm (sref (ref val v89prm) (ref color v90prm) (ref left aprm) (ref right bprm) ))
(pto v88prm (sref (ref val v91prm) (ref color v92prm) (ref left tmpprm) (ref right cprm) ))
) )
))
)

(assert (not 
(exists ((flted248 Int)(flted249 Int)(flted250 Int))(and 
(= flted248 (+ 1 ha))
(= flted249 0)
(= flted250 (+ (+ (+ 2 nb) na) nc))
(<= 0 nc)
(<= 0 nb)
(<= 1 ha)
(<= 0 na)
(tobool  
(rb res flted250 flted249 flted248)
 )
))
))

(check-sat)