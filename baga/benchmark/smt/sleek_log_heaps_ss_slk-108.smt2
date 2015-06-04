(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun nleft () (Field node Int))
(declare-fun nright () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun pq ((?in node) (?n Int) (?mx Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)
(= ?mx 0)

)(exists ((?m1_28 Int)(?m2_29 Int)(?m3_27 Int))(and 
(= ?n (+ (+ ?m2 1) ?m1))
(<= 0 ?d)
(<= ?mx1 ?d)
(<= ?mx2 ?d)
(<= ?d ?mx)
(= (+ ?m3_27 ?m2) ?m1)
(<= 0 ?m3_27)
(<= ?m3_27 1)
(= ?m1_28 ?m1)
(= ?m2_29 ?m2)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref nleft ?m1) (ref nright ?m2) (ref left ?l) (ref right ?r) ))
(pq ?l ?m1_28 ?mx1)
(pq ?r ?m2_29 ?mx2)
) )
)))))
































































































































































(declare-fun l11_7922 () node)
(declare-fun r11_7925 () node)
(declare-fun t () node)
(declare-fun v13prm () Int)
(declare-fun v12 () Int)
(declare-fun tmp1prm () node)
(declare-fun tprm () node)
(declare-fun m67_7919 () Int)
(declare-fun m66_7918 () Int)
(declare-fun m68_7920 () Int)
(declare-fun mx () Int)
(declare-fun mx56_7927 () Int)
(declare-fun mx55_7924 () Int)
(declare-fun d18_7921 () Int)
(declare-fun n () Int)
(declare-fun m69_7923 () Int)
(declare-fun m70_7926 () Int)


(assert 
(exists ((m66 Int)(m67 Int)(m68 Int)(d18 Int)(l11 node)(m69 Int)(mx55 Int)(r11 node)(m70 Int)(mx56 Int))(and 
;lexvar(= tprm t)
(= v13prm v12)
(<= 0 v12)
(= tmp1prm nil)
(distinct tprm nil)
(= m67 m70)
(= m66 m69)
(<= m68 1)
(<= 0 m68)
(= (+ m68 m70) m69)
(<= d18 mx)
(<= mx56 d18)
(<= mx55 d18)
(<= 0 d18)
(= n (+ (+ m70 1) m69))
(tobool (ssep 
(pq l11 m66 mx55)
(pto tprm (sref (ref val d18) (ref nleft m69) (ref nright m70) (ref left l11) (ref right r11) ))
(pq r11 m67 mx56)
) )
))
)

(assert (not 
(and 
(tobool  
(pto tprm (sref (ref val val25prm) (ref nleft nleft25prm) (ref nright nright25prm) (ref left left25prm) (ref right right25prm) ))
 )
)
))

(check-sat)