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





































































































































































































































































































































































(declare-fun v25_9844 () Int)
(declare-fun l17_9845 () node)
(declare-fun r17_9848 () node)
(declare-fun nb () Int)
(declare-fun Anon11 () Int)
(declare-fun nc () Int)
(declare-fun flted155_9843 () Int)
(declare-fun flted154_9842 () Int)
(declare-fun flted153_9841 () Int)
(declare-fun flted157_9854 () Int)
(declare-fun na () Int)
(declare-fun nl17_9846 () Int)
(declare-fun nr17_9849 () Int)
(declare-fun bhl17_9847 () Int)
(declare-fun bhr17_9850 () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun colorprm () Int)
(declare-fun flted156_9853 () Int)
(declare-fun color () Int)
(declare-fun ha5_9851 () Int)
(declare-fun ha6_9852 () Int)
(declare-fun ha () Int)
(declare-fun v58prm () Int)


(assert 
(exists ((flted153 Int)(flted154 Int)(flted155 Int)(v25 Int)(l17 node)(nl17 Int)(bhl17 Int)(r17 node)(nr17 Int)(bhr17 Int)(ha5 Int)(ha6 Int)(flted156 Int)(flted157 Int))(and 
;lexvar(= flted155 1)
(= flted154 0)
(= flted153 0)
(= flted157 1)
(= na (+ (+ nr17 1) nl17))
(= bhl17 ha)
(= bhr17 ha)
(= aprm a)
(= bprm b)
(= cprm c)
(= colorprm color)
(= flted156 0)
(= color 1)
(= ha5 ha)
(= ha6 ha)
(= v58prm 0)
(tobool (ssep 
(pto aprm (sref (ref val v25) (ref color flted155) (ref left l17) (ref right r17) ))
(rb l17 nl17 flted154 bhl17)
(rb r17 nr17 flted153 bhr17)
(rb b nb Anon11 ha5)
(rb c nc flted156 ha6)
) )
))
)

(assert (not 
(and 
(tobool  
(pto aprm (sref (ref val val13prm) (ref color color14prm) (ref left left13prm) (ref right right13prm) ))
 )
)
))

(check-sat)