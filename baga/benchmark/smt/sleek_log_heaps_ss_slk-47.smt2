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
(declare-fun l7_2353 () node)
(declare-fun r7_2356 () node)
(declare-fun v20prm () Int)
(declare-fun dprm () NUM)
(declare-fun v13prm () Int)
(declare-fun lprm () node)
(declare-fun l2 () node)
(declare-fun rprm () node)
(declare-fun r2 () node)
(declare-fun v12 () Int)
(declare-fun d2 () Int)
(declare-fun m1 () Int)
(declare-fun m2 () Int)
(declare-fun m1prm () Int)
(declare-fun m2prm () Int)
(declare-fun m39 () Int)
(declare-fun m40 () Int)
(declare-fun m41 () Int)
(declare-fun mx1 () Int)
(declare-fun mx20 () Int)
(declare-fun mx21 () Int)
(declare-fun d7 () Int)
(declare-fun m23 () Int)
(declare-fun m43 () Int)
(declare-fun m42 () Int)
(declare-fun m45_2350 () Int)
(declare-fun m44_2349 () Int)
(declare-fun m46_2351 () Int)
(declare-fun mx2 () Int)
(declare-fun mx23_2358 () Int)
(declare-fun mx22_2355 () Int)
(declare-fun d8_2352 () Int)
(declare-fun m22 () Int)
(declare-fun m47_2354 () Int)
(declare-fun m48_2357 () Int)


(assert 
(exists ((m44 Int)(m45 Int)(m46 Int)(d8 Int)(l7 node)(m47 Int)(mx22 Int)(r7 node)(m48 Int)(mx23 Int))(and 
;lexvar(= v20prm d7)
(= dprm d2)
(= v13prm v12)
(= m1prm m1)
(= m2prm m2)
(= lprm l2)
(= rprm r2)
(<= (+ 0 m2) m1)
(<= m1 (+ 1 m2))
(<= mx1 d2)
(<= mx2 d2)
(<= 0 v12)
(<= v12 d2)
(= m23 m1)
(= m22 m2)
(distinct m1prm 0)
(distinct m2prm 0)
(= m39 m42)
(= m40 m43)
(<= m41 1)
(<= 0 m41)
(= (+ m41 m42) m43)
(<= d7 mx1)
(<= mx20 d7)
(<= mx21 d7)
(<= 0 d7)
(= m23 (+ (+ m42 1) m43))
(= m45 m48)
(= m44 m47)
(<= m46 1)
(<= 0 m46)
(= (+ m46 m48) m47)
(<= d8 mx2)
(<= mx23 d8)
(<= mx22 d8)
(<= 0 d8)
(= m22 (+ (+ m48 1) m47))
(tobool (ssep 
(pq l6 m40 mx21)
(pto lprm (sref (ref val d7) (ref nleft m43) (ref nright m42) (ref left l6) (ref right r6) ))
(pq r6 m39 mx20)
(pto rprm (sref (ref val d8) (ref nleft m47) (ref nright m48) (ref left l7) (ref right r7) ))
(pq l7 m44 mx22)
(pq r7 m45 mx23)
) )
))
)

(assert (not 
(and 
(tobool  
(pto rprm (sref (ref val val7prm) (ref nleft nleft7prm) (ref nright nright7prm) (ref left left7prm) (ref right right7prm) ))
 )
)
))

(check-sat)