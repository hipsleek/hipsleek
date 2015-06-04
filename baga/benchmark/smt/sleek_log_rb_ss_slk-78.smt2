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
(declare-fun flted189_11820 () Int)
(declare-fun flted188_11819 () Int)
(declare-fun flted187_11818 () Int)
(declare-fun flted186_11817 () Int)
(declare-fun color () Int)
(declare-fun v63_11821 () Int)
(declare-fun v64_11822 () Int)
(declare-fun h_11823 () Int)
(declare-fun h_11824 () Int)
(declare-fun h_11825 () Int)
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