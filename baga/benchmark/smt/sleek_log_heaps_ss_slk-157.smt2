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
(declare-fun v29 () node)
(declare-fun val2 () Int)
(declare-fun nright () Int)
(declare-fun v37 () Int)
(declare-fun right () node)
(declare-fun r12 () node)
(declare-fun ma3 () Int)
(declare-fun n6 () Int)
(declare-fun mx60 () Int)
(declare-fun n4 () Int)
(declare-fun tmpv1 () Int)
(declare-fun t () node)
(declare-fun tprm () node)
(declare-fun m74 () Int)
(declare-fun m72 () Int)
(declare-fun m71 () Int)
(declare-fun mx58 () Int)
(declare-fun mx57 () Int)
(declare-fun d19 () Int)
(declare-fun v13prm () Int)
(declare-fun m75 () Int)
(declare-fun m73 () Int)
(declare-fun res () node)
(declare-fun v12 () Int)
(declare-fun mx () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= res tprm)
(= val2 d19)
(= nright m75)
(= v37 (+ 1 m75))
(= right r12)
(<= 0 mx60)
(<= 0 n4)
(= n6 (+ 1 n4))
(<= 0 mx58)
(<= 0 m74)
(= mx60 mx58)
(= n4 m74)
(= tmpv1 d19)
(= tprm t)
(= v13prm v12)
(<= 0 v12)
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
(< d19 v13prm)
(< m75 m73)
(tobool (ssep 
(pq l12 m72 mx57)
(pq v29 n6 ma3)
(pto tprm (sref (ref val v13prm) (ref nleft m73) (ref nright v37) (ref left l12) (ref right v29) ))
) )
)
)

(assert (not 
(exists ((n13 Int)(ma8 Int))(and 
(= n13 (+ 1 n))
(<= 0 mx)
(<= 0 n)
(tobool  
(pq res n13 ma8)
 )
))
))

(check-sat)