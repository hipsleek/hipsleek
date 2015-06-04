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
(declare-fun flted189_12081 () Int)
(declare-fun flted188_12080 () Int)
(declare-fun flted187_12079 () Int)
(declare-fun flted186_12078 () Int)
(declare-fun color () Int)
(declare-fun v63_12082 () Int)
(declare-fun v64_12083 () Int)
(declare-fun h_12084 () Int)
(declare-fun h_12085 () Int)
(declare-fun h_12086 () Int)
(declare-fun h () Int)
(declare-fun colorprm () Int)


(assert 
(exists ((flted186 Int)(flted187 Int)(flted188 Int)(flted189 Int)(v63prm Int)(v64prm Int))(and 
;lexvar(= aprm a)
(= bprm b)
(= cprm c)
(= dprm d)
(= colorprm color)
(= flted189 0)
(= flted188 0)
(= flted187 0)
(= flted186 0)
(= color 1)
(= v63prm 0)
(= v64prm 1)
(tobool (ssep 
(rb a na flted189 h)
(rb b nb flted188 h)
(rb c nc flted187 h)
(rb d nd flted186 h)
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