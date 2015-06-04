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
































































































































































(declare-fun l12 () node)
(declare-fun tmpprm () node)
(declare-fun r12 () node)
(declare-fun t () node)
(declare-fun v12 () Int)
(declare-fun tmp1prm () node)
(declare-fun tprm () node)
(declare-fun m74 () Int)
(declare-fun m72 () Int)
(declare-fun m71 () Int)
(declare-fun mx () Int)
(declare-fun mx58 () Int)
(declare-fun mx57 () Int)
(declare-fun n () Int)
(declare-fun d19 () Int)
(declare-fun m75 () Int)
(declare-fun m73 () Int)
(declare-fun v13prm () Int)


(assert 
(and 
;lexvar(= tmpprm r12)
(= tprm t)
(= v13prm v12)
(<= 0 v12)
(= tmp1prm nil)
(distinct tprm nil)
(= m74 m75)
(= m72 m73)
(<= m71 1)
(<= 0 m71)
(= (+ m71 m75) m73)
(<= d19 mx)
(<= mx58 d19)
(<= mx57 d19)
(<= 0 d19)
(= n (+ (+ m75 1) m73))
(<= v13prm d19)
(< m75 m73)
(tobool (ssep 
(pq l12 m72 mx57)
(pto tprm (sref (ref val d19) (ref nleft m73) (ref nright m75) (ref left l12) (ref right r12) ))
(pq r12 m74 mx58)
) )
)
)

(assert (not 
(and 
(<= 0 v13prm)
(tobool  
(pq tmpprm n10 mx62)
 )
)
))

(check-sat)