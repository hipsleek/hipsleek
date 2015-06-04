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
(declare-fun v20_5787 () Int)
(declare-fun l12_5788 () node)
(declare-fun Anon6_5790 () Int)
(declare-fun r12_5792 () node)
(declare-fun Anon7_5794 () Int)
(declare-fun nc () Int)
(declare-fun flted112_5786 () Int)
(declare-fun flted116_5799 () Int)
(declare-fun nb () Int)
(declare-fun nl12_5789 () Int)
(declare-fun nr12_5793 () Int)
(declare-fun bhr12_5795 () Int)
(declare-fun bhl12_5791 () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun cprm () node)
(declare-fun flted117_5800 () Int)
(declare-fun flted115_5798 () Int)
(declare-fun flted114_5797 () Int)
(declare-fun flted113_5796 () Int)
(declare-fun h () Int)
(declare-fun b () node)
(declare-fun c () node)


(assert 
(exists ((flted112 Int)(v20 Int)(l12 node)(nl12 Int)(Anon6 Int)(bhl12 Int)(r12 node)(nr12 Int)(Anon7 Int)(bhr12 Int)(flted113 Int)(flted114 Int)(flted115 Int)(flted116 Int)(flted117 Int))(and 
;lexvar(= flted112 0)
(= flted116 0)
(= nb (+ (+ nr12 1) nl12))
(= bhl12 bhr12)
(= flted115 (+ bhl12 1))
(= aprm a)
(= bprm b)
(= cprm c)
(= flted117 0)
(= flted115 (+ 1 h))
(= flted114 0)
(= flted113 (+ 1 h))
(distinct b nil)
(distinct c nil)
(tobool (ssep 
(rb a na flted117 h)
(pto bprm (sref (ref val v20) (ref color flted112) (ref left l12) (ref right r12) ))
(rb l12 nl12 Anon6 bhl12)
(rb r12 nr12 Anon7 bhr12)
(rb c nc flted114 flted113)
) )
))
)

(assert (not 
(and 
(tobool  
(pto bprm (sref (ref val val2prm) (ref color color3prm) (ref left left2prm) (ref right right2prm) ))
 )
)
))

(check-sat)