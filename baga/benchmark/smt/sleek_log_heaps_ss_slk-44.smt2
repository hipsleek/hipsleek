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
































































































































































(declare-fun l4 () node)
(declare-fun r4 () node)
(declare-fun dprm () NUM)
(declare-fun m2prm () Int)
(declare-fun lprm () node)
(declare-fun l2 () node)
(declare-fun rprm () node)
(declare-fun r2 () node)
(declare-fun mx2 () Int)
(declare-fun v12 () Int)
(declare-fun d2 () Int)
(declare-fun m1 () Int)
(declare-fun m22 () Int)
(declare-fun m2 () Int)
(declare-fun m1prm () Int)
(declare-fun m32 () Int)
(declare-fun m30 () Int)
(declare-fun m29 () Int)
(declare-fun mx1 () Int)
(declare-fun mx17 () Int)
(declare-fun mx16 () Int)
(declare-fun m23 () Int)
(declare-fun m31 () Int)
(declare-fun m33 () Int)
(declare-fun v13prm () Int)
(declare-fun d4 () Int)


(assert 
(and 
;lexvar(= m2prm 0)
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
(= m32 m33)
(= m30 m31)
(<= m29 1)
(<= 0 m29)
(= (+ m29 m33) m31)
(<= d4 mx1)
(<= mx17 d4)
(<= mx16 d4)
(<= 0 d4)
(= m23 (+ (+ m33 1) m31))
(< v13prm d4)
(tobool (ssep 
(pq l4 m30 mx16)
(pto lprm (sref (ref val d4) (ref nleft m31) (ref nright m33) (ref left l4) (ref right r4) ))
(pq r4 m32 mx17)
(pq r2 m22 mx2)
) )
)
)

(assert (not 
(and 
(tobool  
(pto lprm (sref (ref val val4prm) (ref nleft nleft4prm) (ref nright nright4prm) (ref left left4prm) (ref right right4prm) ))
 )
)
))

(check-sat)