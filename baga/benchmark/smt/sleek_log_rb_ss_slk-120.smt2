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





































































































































































































































































































































































(declare-fun tmp_18701 () node)
(declare-fun v83prm () node)
(declare-fun v87_18700 () Int)
(declare-fun v86_18699 () Int)
(declare-fun v85_18698 () Int)
(declare-fun v84_18697 () Int)
(declare-fun flted239_18694 () Int)
(declare-fun flted240_18695 () Int)
(declare-fun flted241_18696 () Int)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun ha_18702 () Int)
(declare-fun ha_18703 () Int)
(declare-fun res () node)
(declare-fun nc () Int)
(declare-fun nb () Int)
(declare-fun ha () Int)
(declare-fun na () Int)


(assert 
(exists ((flted239 Int)(flted240 Int)(flted241 Int)(v84prm Int)(v85prm Int)(v86prm Int)(v87prm Int)(tmpprm node))(and 
;lexvar(= res v83prm)
(= v87prm 0)
(= v86prm 0)
(= v85prm 1)
(= v84prm 0)
(= flted239 0)
(= flted240 0)
(= flted241 0)
(= cprm c)
(= bprm b)
(= aprm a)
(tobool (ssep 
(rb a na flted241 ha)
(rb b nb flted240 ha)
(rb c nc flted239 ha)
(pto tmpprm (sref (ref val v84prm) (ref color v85prm) (ref left bprm) (ref right cprm) ))
(pto v83prm (sref (ref val v86prm) (ref color v87prm) (ref left aprm) (ref right tmpprm) ))
) )
))
)

(assert (not 
(exists ((flted242 Int)(flted243 Int)(flted244 Int))(and 
(= flted242 (+ 1 ha))
(= flted243 0)
(= flted244 (+ (+ (+ 2 nb) na) nc))
(<= 0 nc)
(<= 0 nb)
(<= 1 ha)
(<= 0 na)
(tobool  
(rb res flted244 flted243 flted242)
 )
))
))

(check-sat)