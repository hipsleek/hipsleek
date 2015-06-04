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
































































































































































(declare-fun l1 () node)
(declare-fun r1 () node)
(declare-fun tprm () node)
(declare-fun t () node)
(declare-fun m5 () Int)
(declare-fun m6 () Int)
(declare-fun m7 () Int)
(declare-fun mx () Int)
(declare-fun mx3 () Int)
(declare-fun mx4 () Int)
(declare-fun d1 () Int)
(declare-fun n () Int)
(declare-fun m8 () Int)
(declare-fun m9 () Int)
(declare-fun vprm () Int)
(declare-fun v1prm () Int)


(assert 
(and 
;lexvar(< 0 n)
(= tprm t)
(= m5 m8)
(= m6 m9)
(<= m7 1)
(<= 0 m7)
(= (+ m7 m8) m9)
(<= d1 mx)
(<= mx3 d1)
(<= mx4 d1)
(<= 0 d1)
(= n (+ (+ m8 1) m9))
(= vprm m9)
(= v1prm 0)
(distinct vprm v1prm)
(tobool (ssep 
(pq l1 m6 mx4)
(pto tprm (sref (ref val d1) (ref nleft m9) (ref nright m8) (ref left l1) (ref right r1) ))
(pq r1 m5 mx3)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)