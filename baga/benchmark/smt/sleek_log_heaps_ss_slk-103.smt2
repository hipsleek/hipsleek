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
































































































































































(declare-fun tleft_7655 () node)
(declare-fun tright_7656 () node)
(declare-fun m63 () Int)
(declare-fun tprm () node)
(declare-fun t () node)
(declare-fun m61 () Int)
(declare-fun mx38 () Int)
(declare-fun m62 () Int)
(declare-fun mx39 () Int)
(declare-fun m65 () Int)
(declare-fun m64 () Int)
(declare-fun maxi6 () Int)
(declare-fun mx1 () Int)
(declare-fun mx2 () Int)
(declare-fun mx48 () Int)
(declare-fun mx49 () Int)
(declare-fun v13_7657 () Int)
(declare-fun max8_7648 () Int)
(declare-fun max9_7649 () Int)
(declare-fun mx53_7650 () Int)
(declare-fun mx54_7651 () Int)
(declare-fun tval_7652 () Int)
(declare-fun mx41 () Int)
(declare-fun mx40 () Int)
(declare-fun d17 () Int)
(declare-fun tnleft_7658 () Int)
(declare-fun tnleft_7653 () Int)
(declare-fun tnright_7659 () Int)
(declare-fun tnright_7654 () Int)
(declare-fun res () Int)
(declare-fun mx () Int)
(declare-fun n () Int)


(assert 
(exists ((max8 Int)(max9 Int)(mx53 Int)(mx54 Int)(tvalprm Int)(tnleftprm Int)(tnrightprm Int)(tleftprm node)(trightprm node)(v13prm Int))(and 
;lexvar(distinct m64 0)
(= n (+ (+ m64 1) m65))
(<= 0 d17)
(<= mx39 d17)
(<= mx38 d17)
(<= d17 mx)
(= (+ m63 m64) m65)
(<= 0 m63)
(<= m63 1)
(= m62 m65)
(= m61 m64)
(= tprm t)
(< 0 n)
(distinct m65 0)
(= mx1 mx39)
(= mx2 mx38)
(<= 0 m61)
(<= 0 mx38)
(<= 0 m62)
(<= 0 mx39)
(= (+ (+ 1 tnleftprm) tnrightprm) (+ m64 m65))
(<= (+ 0 tnrightprm) tnleftprm)
(<= tnleftprm (+ 1 tnrightprm))
(<= mx49 mx1)
(<= mx48 mx2)
;eqmax(<= 0 v13prm)
(<= v13prm maxi6)
(<= 0 mx1)
(<= 0 mx2)
(= mx41 mx49)
(= mx40 mx48)
(<= 0 tnrightprm)
(<= 0 mx48)
(<= 0 tnleftprm)
(<= 0 mx49)
(<= mx53 mx41)
(<= mx54 mx40)
;eqmax;eqmax(<= tvalprm max9)
(<= mx53 tvalprm)
(<= mx54 tvalprm)
(<= 0 tvalprm)
(<= 0 mx41)
(<= 0 mx40)
(= res d17)
(tobool (ssep 
(pq tleftprm tnleftprm mx53)
(pq trightprm tnrightprm mx54)
(pto tprm (sref (ref val tvalprm) (ref nleft tnleftprm) (ref nright tnrightprm) (ref left tleftprm) (ref right trightprm) ))
) )
))
)

(assert (not 
(exists ((flted3 Int)(mx50 Int))(and 
(<= res mx)
(<= mx50 res)
(= (+ flted3 1) n)
(<= 0 mx)
(<= 0 n)
(tobool  
(pq tprm flted3 mx50)
 )
))
))

(check-sat)