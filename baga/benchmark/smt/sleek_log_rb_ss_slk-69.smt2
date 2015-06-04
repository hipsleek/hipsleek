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





































































































































































































































































































































































(declare-fun v24_9772 () Int)
(declare-fun l16_9773 () node)
(declare-fun r16_9776 () node)
(declare-fun nb () Int)
(declare-fun Anon10 () Int)
(declare-fun nc () Int)
(declare-fun flted150_9771 () Int)
(declare-fun flted149_9770 () Int)
(declare-fun flted148_9769 () Int)
(declare-fun flted152_9782 () Int)
(declare-fun na () Int)
(declare-fun nl16_9774 () Int)
(declare-fun nr16_9777 () Int)
(declare-fun bhl16_9775 () Int)
(declare-fun bhr16_9778 () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun colorprm () Int)
(declare-fun flted151_9781 () Int)
(declare-fun color () Int)
(declare-fun ha3_9779 () Int)
(declare-fun ha4_9780 () Int)
(declare-fun ha () Int)
(declare-fun v58prm () Int)


(assert 
(exists ((flted148 Int)(flted149 Int)(flted150 Int)(v24 Int)(l16 node)(nl16 Int)(bhl16 Int)(r16 node)(nr16 Int)(bhr16 Int)(ha3 Int)(ha4 Int)(flted151 Int)(flted152 Int))(and 
;lexvar(= flted150 1)
(= flted149 0)
(= flted148 0)
(= flted152 1)
(= na (+ (+ nr16 1) nl16))
(= bhl16 ha)
(= bhr16 ha)
(= aprm a)
(= bprm b)
(= cprm c)
(= colorprm color)
(= flted151 0)
(= color 0)
(= ha3 ha)
(= ha4 ha)
(= v58prm 0)
(tobool (ssep 
(pto aprm (sref (ref val v24) (ref color flted150) (ref left l16) (ref right r16) ))
(rb l16 nl16 flted149 bhl16)
(rb r16 nr16 flted148 bhr16)
(rb b nb Anon10 ha3)
(rb c nc flted151 ha4)
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