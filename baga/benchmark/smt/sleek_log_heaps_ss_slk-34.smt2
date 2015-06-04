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
































































































































































(declare-fun lprm () node)
(declare-fun m13 () Int)
(declare-fun rprm () node)
(declare-fun r2 () node)
(declare-fun m2prm () Int)
(declare-fun m1prm () Int)
(declare-fun m14 () NUM)
(declare-fun m12 () Int)
(declare-fun flted1_1582 () Int)
(declare-fun mx10_1583 () Int)
(declare-fun n () Int)
(declare-fun mx () Int)
(declare-fun v10prm () Int)
(declare-fun res () Int)
(declare-fun m1 () Int)
(declare-fun m2 () Int)
(declare-fun mx2 () Int)
(declare-fun mx1 () Int)


(assert 
(exists ((flted1 Int)(mx10 Int))(and 
;lexvar(< m2prm m14)
(= m13 m2)
(= m12 m1)
(<= m1 (+ 1 m2))
(<= (+ 0 m2) m1)
(< 0 (+ m2 m1))
(= rprm r2)
(= m2prm m2)
(= m14 m1)
(= (+ m1prm 1) m14)
(= n m12)
(= mx mx1)
(<= 0 m12)
(<= 0 mx1)
(= (+ flted1 1) n)
(<= 0 v10prm)
(<= v10prm mx)
(<= mx10 mx)
(<= 0 n)
(<= 0 mx)
(= res v10prm)
(tobool (ssep 
(pq r2 m13 mx2)
(pq lprm flted1 mx10)
) )
))
)

(assert (not 
(exists ((mx11 Int)(mx12 Int)(maxi2 NUM))(and 
(<= res maxi2)
(<= 0 res)
;eqmax(<= mx12 mx2)
(<= mx11 mx1)
(<= m1prm (+ 1 m2prm))
(<= (+ 0 m2prm) m1prm)
(= (+ (+ 1 m1prm) m2prm) (+ m2 m1))
(<= 0 mx2)
(<= 0 mx1)
(tobool (ssep 
(pq lprm m1prm mx11)
(pq rprm m2prm mx12)
) )
))
))

(check-sat)