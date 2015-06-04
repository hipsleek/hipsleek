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
































































































































































(declare-fun rprm () node)
(declare-fun m15 () Int)
(declare-fun lprm () node)
(declare-fun l2 () node)
(declare-fun m1prm () Int)
(declare-fun m2prm () Int)
(declare-fun m17 () NUM)
(declare-fun m16 () Int)
(declare-fun flted2_1662 () Int)
(declare-fun mx13_1663 () Int)
(declare-fun n () Int)
(declare-fun mx () Int)
(declare-fun v11prm () Int)
(declare-fun res () Int)
(declare-fun m1 () Int)
(declare-fun m2 () Int)
(declare-fun mx2 () Int)
(declare-fun mx1 () Int)


(assert 
(exists ((flted2 Int)(mx13 Int))(and 
;lexvar(<= m1prm m17)
(= m16 m2)
(= m15 m1)
(<= m1 (+ 1 m2))
(<= (+ 0 m2) m1)
(< 0 (+ m2 m1))
(= lprm l2)
(= m17 m2)
(= m1prm m1)
(= (+ m2prm 1) m17)
(= n m16)
(= mx mx2)
(<= 0 m16)
(<= 0 mx2)
(= (+ flted2 1) n)
(<= 0 v11prm)
(<= v11prm mx)
(<= mx13 mx)
(<= 0 n)
(<= 0 mx)
(= res v11prm)
(tobool (ssep 
(pq l2 m15 mx1)
(pq rprm flted2 mx13)
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