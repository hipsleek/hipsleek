(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


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
(declare-fun flted177_11501 () Int)
(declare-fun flted176_11500 () Int)
(declare-fun flted175_11499 () Int)
(declare-fun flted174_11498 () Int)
(declare-fun color () Int)
(declare-fun v63_11502 () Int)
(declare-fun v64_11503 () Int)
(declare-fun h_11504 () Int)
(declare-fun h_11505 () Int)
(declare-fun h_11506 () Int)
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
(exists ((ha13 Int)(ha14 Int)(flted180 Int)(flted181 Int))(and 
(= ha14 ha)
(= ha13 ha)
(= colorprm 1)
(= flted180 0)
(= flted181 1)
(tobool (ssep 
(rb tmpprm na7 flted181 ha)
(rb cprm nb7 Anon11 ha13)
(rb dprm nc7 flted180 ha14)
) )
))
))

(check-sat)