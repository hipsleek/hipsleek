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
































































































































































(declare-fun tleftprm () node)
(declare-fun trightprm () node)
(declare-fun tmpprm () Int)
(declare-fun maxi3_6948 () NUM)
(declare-fun mx43_6947 () Int)
(declare-fun mx42_6946 () Int)
(declare-fun mx38 () Int)
(declare-fun mx () Int)
(declare-fun m63 () Int)
(declare-fun m62 () Int)
(declare-fun tprm () node)
(declare-fun t () node)
(declare-fun n () Int)
(declare-fun m65 () Int)
(declare-fun m64 () Int)
(declare-fun d17 () Int)
(declare-fun mx1 () Int)
(declare-fun mx39 () Int)
(declare-fun m61 () Int)
(declare-fun r10 () node)
(declare-fun mx2 () Int)
(declare-fun v13prm () Int)
(declare-fun tvalprm () Int)
(declare-fun tnrightprm () Int)
(declare-fun tnleftprm () Int)


(assert 
(exists ((mx42 Int)(mx43 Int)(maxi3 NUM))(and 
;lexvar(= tmpprm tvalprm)
(<= 0 mx2)
(<= 0 mx1)
(<= v13prm maxi3)
(<= 0 v13prm)
;eqmax(<= mx43 mx2)
(<= mx42 mx1)
(<= tnleftprm (+ 1 tnrightprm))
(<= (+ 0 tnrightprm) tnleftprm)
(= (+ (+ 1 tnleftprm) tnrightprm) (+ m64 m65))
(<= 0 mx39)
(<= 0 m62)
(= r10 nil)
(= m61 0)
(= mx38 0)
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
(= m64 0)
(= tvalprm d17)
(= mx1 mx39)
(= mx2 0)
(tobool (ssep 
(pq tleftprm tnleftprm mx42)
(pq trightprm tnrightprm mx43)
) )
))
)

(assert (not 
(exists ((m18 Int)(m19 Int))(and 
(= m19 tnrightprm)
(= m18 tnleftprm)
(<= v13prm tvalprm)
(<= 0 v13prm)
(<= mx40 tvalprm)
(<= mx41 tvalprm)
(<= tnleftprm (+ 1 tnrightprm))
(<= (+ 0 tnrightprm) tnleftprm)
(tobool (ssep 
(pq tleftprm m18 mx41)
(pq trightprm m19 mx40)
) )
))
))

(check-sat)