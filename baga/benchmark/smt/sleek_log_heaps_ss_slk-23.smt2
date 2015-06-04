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
































































































































































(declare-fun tleft_1134 () node)
(declare-fun tright_1135 () node)
(declare-fun d1 () Int)
(declare-fun m7 () Int)
(declare-fun tprm () node)
(declare-fun t () node)
(declare-fun m5 () Int)
(declare-fun mx3 () Int)
(declare-fun m6 () Int)
(declare-fun mx4 () Int)
(declare-fun m9 () Int)
(declare-fun m8 () Int)
(declare-fun mx8_1129 () Int)
(declare-fun mx9_1130 () Int)
(declare-fun maxi1_1131 () Int)
(declare-fun mx1 () Int)
(declare-fun mx2 () Int)
(declare-fun tnleft_1136 () Int)
(declare-fun tnleft_1132 () Int)
(declare-fun tnright_1137 () Int)
(declare-fun tnright_1133 () Int)
(declare-fun res () Int)
(declare-fun mx () Int)
(declare-fun n () Int)


(assert 
(exists ((mx8 Int)(mx9 Int)(maxi1 Int)(tnleftprm Int)(tnrightprm Int)(tleftprm node)(trightprm node))(and 
;lexvar(distinct m8 0)
(= n (+ (+ m8 1) m9))
(<= 0 d1)
(<= mx4 d1)
(<= mx3 d1)
(<= d1 mx)
(= (+ m7 m8) m9)
(<= 0 m7)
(<= m7 1)
(= m6 m9)
(= m5 m8)
(= tprm t)
(< 0 n)
(distinct m9 0)
(= mx1 mx4)
(= mx2 mx3)
(<= 0 m5)
(<= 0 mx3)
(<= 0 m6)
(<= 0 mx4)
(= (+ (+ 1 tnleftprm) tnrightprm) (+ m8 m9))
(<= (+ 0 tnrightprm) tnleftprm)
(<= tnleftprm (+ 1 tnrightprm))
(<= mx8 mx1)
(<= mx9 mx2)
;eqmax(<= 0 res)
(<= res maxi1)
(<= 0 mx1)
(<= 0 mx2)
(tobool (ssep 
(pq tleftprm tnleftprm mx8)
(pq trightprm tnrightprm mx9)
(pto tprm (sref (ref val d1) (ref nleft tnleftprm) (ref nright tnrightprm) (ref left tleftprm) (ref right trightprm) ))
) )
))
)

(assert (not 
(exists ((flted Int)(mx5 Int))(and 
(<= mx5 mx)
(<= res mx)
(<= 0 res)
(= (+ flted 1) n)
(<= 0 mx)
(<= 0 n)
(tobool  
(pq tprm flted mx5)
 )
))
))

(check-sat)