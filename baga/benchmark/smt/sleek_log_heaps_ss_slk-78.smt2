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
































































































































































(declare-fun l6 () node)
(declare-fun r6 () node)
(declare-fun l8 () node)
(declare-fun r8 () node)
(declare-fun m49 () Int)
(declare-fun mx21 () Int)
(declare-fun mx20 () Int)
(declare-fun d7 () Int)
(declare-fun m41 () Int)
(declare-fun m40 () Int)
(declare-fun m43 () Int)
(declare-fun m39 () Int)
(declare-fun m42 () Int)
(declare-fun m22 () Int)
(declare-fun m23 () Int)
(declare-fun rprm () node)
(declare-fun lprm () node)
(declare-fun m2prm () Int)
(declare-fun m1prm () Int)
(declare-fun d11 () Int)
(declare-fun d2 () Int)
(declare-fun d9 () Int)
(declare-fun m52 () Int)
(declare-fun mx25 () Int)
(declare-fun m50 () Int)
(declare-fun mx24 () Int)
(declare-fun v13prm () Int)
(declare-fun max4_5857 () Int)
(declare-fun max5_5858 () Int)
(declare-fun mx34_5859 () Int)
(declare-fun mx35_5860 () Int)
(declare-fun v32_5861 () Int)
(declare-fun mx29 () Int)
(declare-fun mx28 () Int)
(declare-fun m51_5862 () Int)
(declare-fun m51 () Int)
(declare-fun m53_5863 () Int)
(declare-fun m53 () Int)
(declare-fun l2 () node)
(declare-fun r2 () node)
(declare-fun m2 () Int)
(declare-fun m1 () Int)
(declare-fun dprm () Int)
(declare-fun v12 () Int)
(declare-fun mx2 () Int)
(declare-fun mx1 () Int)


(assert 
(exists ((max4 Int)(max5 Int)(mx34 Int)(mx35 Int)(v32prm Int))(and 
;lexvar(< v13prm d9)
(< d7 d9)
(= m22 (+ (+ m53 1) m51))
(<= 0 d9)
(<= mx24 d9)
(<= mx25 d9)
(<= d9 mx2)
(= (+ m49 m53) m51)
(<= 0 m49)
(<= m49 1)
(= m50 m51)
(= m52 m53)
(= m23 (+ (+ m42 1) m43))
(<= 0 d7)
(<= mx21 d7)
(<= mx20 d7)
(<= d7 mx1)
(= (+ m41 m42) m43)
(<= 0 m41)
(<= m41 1)
(= m40 m43)
(= m39 m42)
(distinct m2prm 0)
(distinct m1prm 0)
(= m22 m2)
(= m23 m1)
(<= v12 d2)
(<= 0 v12)
(<= mx2 d2)
(<= mx1 d2)
(<= m1 (+ 1 m2))
(<= (+ 0 m2) m1)
(= rprm r2)
(= lprm l2)
(= m2prm m2)
(= m1prm m1)
(= v13prm v12)
(= d11 d2)
(= dprm d9)
(= mx29 mx24)
(= mx28 mx25)
(<= 0 m52)
(<= 0 mx25)
(<= 0 m50)
(<= 0 mx24)
(<= mx34 mx29)
(<= mx35 mx28)
;eqmax;eqmax(<= v32prm max5)
(<= mx34 v32prm)
(<= mx35 v32prm)
(<= 0 v32prm)
(<= 0 mx29)
(<= 0 mx28)
(tobool (ssep 
(pq l6 m40 mx21)
(pto lprm (sref (ref val d7) (ref nleft m43) (ref nright m42) (ref left l6) (ref right r6) ))
(pq r6 m39 mx20)
(pto rprm (sref (ref val d9) (ref nleft m51) (ref nright m53) (ref left l8) (ref right r8) ))
(pq l8 m51 mx34)
(pq r8 m53 mx35)
) )
))
)

(assert (not 
(exists ((m54 Int)(m55 Int)(maxx Int)(max1 Int)(mx30 Int)(mx31 Int))(and 
(= m55 m2)
(= m54 m1)
(<= 0 dprm)
(<= mx31 dprm)
(<= mx30 dprm)
(<= dprm max1)
;eqmax;eqmax(<= mx31 mx2)
(<= mx30 mx1)
(<= 0 mx2)
(<= 0 mx1)
(tobool (ssep 
(pq l2 m54 mx30)
(pq r2 m55 mx31)
) )
))
))

(check-sat)