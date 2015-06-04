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





































































































































































































































































































































































(declare-fun tmp_9557 () node)
(declare-fun v53prm () node)
(declare-fun v57_9556 () Int)
(declare-fun v56_9555 () Int)
(declare-fun v55_9554 () Int)
(declare-fun v54_9553 () Int)
(declare-fun flted142_9550 () Int)
(declare-fun flted143_9551 () Int)
(declare-fun flted144_9552 () Int)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun ha_9558 () Int)
(declare-fun ha_9559 () Int)
(declare-fun res () node)
(declare-fun nc () Int)
(declare-fun nb () Int)
(declare-fun ha () Int)
(declare-fun na () Int)


(assert 
(exists ((flted142 Int)(flted143 Int)(flted144 Int)(v54prm Int)(v55prm Int)(v56prm Int)(v57prm Int)(tmpprm node))(and 
;lexvar(= res v53prm)
(= v57prm 0)
(= v56prm 0)
(= v55prm 1)
(= v54prm 0)
(= flted142 0)
(= flted143 0)
(= flted144 0)
(= cprm c)
(= bprm b)
(= aprm a)
(tobool (ssep 
(rb a na flted144 ha)
(rb b nb flted143 ha)
(rb c nc flted142 ha)
(pto tmpprm (sref (ref val v54prm) (ref color v55prm) (ref left aprm) (ref right bprm) ))
(pto v53prm (sref (ref val v56prm) (ref color v57prm) (ref left tmpprm) (ref right cprm) ))
) )
))
)

(assert (not 
(exists ((flted145 Int)(flted146 Int)(flted147 Int))(and 
(= flted145 (+ 1 ha))
(= flted146 0)
(= flted147 (+ (+ (+ 2 nb) na) nc))
(<= 0 nc)
(<= 0 nb)
(<= 1 ha)
(<= 0 na)
(tobool  
(rb res flted147 flted146 flted145)
 )
))
))

(check-sat)