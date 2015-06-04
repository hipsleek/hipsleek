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





































































































































































































































































































































































(declare-fun na () Int)
(declare-fun nb () Int)
(declare-fun nc () Int)
(declare-fun nd () Int)
(declare-fun tmpprm () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun dprm () node)
(declare-fun d () node)
(declare-fun flted177_11380 () Int)
(declare-fun flted176_11379 () Int)
(declare-fun flted175_11378 () Int)
(declare-fun flted174_11377 () Int)
(declare-fun color () Int)
(declare-fun v63_11381 () Int)
(declare-fun v64_11382 () Int)
(declare-fun h_11383 () Int)
(declare-fun h_11384 () Int)
(declare-fun h_11385 () Int)
(declare-fun h () Int)
(declare-fun colorprm () Int)


(assert 
(exists ((flted174 Int)(flted175 Int)(flted176 Int)(flted177 Int)(v63prm Int)(v64prm Int))(and 
;lexvar(= aprm a)
(= bprm b)
(= cprm c)
(= dprm d)
(= colorprm color)
(= flted177 0)
(= flted176 0)
(= flted175 0)
(= flted174 0)
(= color 0)
(= v63prm 0)
(= v64prm 1)
(tobool (ssep 
(rb a na flted177 h)
(rb b nb flted176 h)
(rb c nc flted175 h)
(rb d nd flted174 h)
(pto tmpprm (sref (ref val v63prm) (ref color v64prm) (ref left aprm) (ref right bprm) ))
) )
))
)

(assert (not 
(exists ((ha11 Int)(ha12 Int)(flted178 Int)(flted179 Int))(and 
(= ha12 ha)
(= ha11 ha)
(= colorprm 0)
(= flted178 0)
(= flted179 1)
(tobool (ssep 
(rb tmpprm na7 flted179 ha)
(rb cprm nb7 Anon10 ha11)
(rb dprm nc7 flted178 ha12)
) )
))
))

(check-sat)