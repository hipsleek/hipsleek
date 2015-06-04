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
(declare-fun mx28 () Int)
(declare-fun mx29 () Int)
(declare-fun v36prm () node)
(declare-fun r8 () node)
(declare-fun v35prm () node)
(declare-fun l8 () node)
(declare-fun v34prm () Int)
(declare-fun v33prm () Int)
(declare-fun v32prm () Int)
(declare-fun dprm () Int)
(declare-fun d11 () NUM)
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
(declare-fun m23 () Int)
(declare-fun m43 () Int)
(declare-fun m42 () Int)
(declare-fun m52 () Int)
(declare-fun m50 () Int)
(declare-fun m49 () Int)
(declare-fun mx2 () Int)
(declare-fun mx25 () Int)
(declare-fun mx24 () Int)
(declare-fun m22 () Int)
(declare-fun m51 () Int)
(declare-fun m53 () Int)
(declare-fun d7 () Int)
(declare-fun v13prm () Int)
(declare-fun d9 () Int)


(assert 
(and 
;lexvar(= mx28 mx25)
(= mx29 mx24)
(= v36prm r8)
(= v35prm l8)
(= v34prm m53)
(= v33prm m51)
(= v32prm d9)
(= dprm d9)
(= d11 d2)
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
(= m52 m53)
(= m50 m51)
(<= m49 1)
(<= 0 m49)
(= (+ m49 m53) m51)
(<= d9 mx2)
(<= mx25 d9)
(<= mx24 d9)
(<= 0 d9)
(= m22 (+ (+ m53 1) m51))
(< d7 d9)
(< v13prm d9)
(tobool (ssep 
(pq l6 m40 mx21)
(pto lprm (sref (ref val d7) (ref nleft m43) (ref nright m42) (ref left l6) (ref right r6) ))
(pq r6 m39 mx20)
(pto rprm (sref (ref val d9) (ref nleft m51) (ref nright m53) (ref left l8) (ref right r8) ))
) )
)
)

(assert (not 
;lexvar
))

(check-sat)