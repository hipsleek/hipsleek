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
































































































































































(declare-fun l_101 () node)
(declare-fun r_104 () node)
(declare-fun mx1_103 () Int)
(declare-fun mx2_106 () Int)
(declare-fun d_100 () Int)
(declare-fun mx () Int)
(declare-fun m2_99 () Int)
(declare-fun m_97 () Int)
(declare-fun m3_102 () Int)
(declare-fun m1_98 () Int)
(declare-fun m4_105 () Int)
(declare-fun tprm () node)
(declare-fun t () node)
(declare-fun n () Int)


(assert 
(exists ((m Int)(m1 Int)(m2 Int)(d Int)(l node)(m3 Int)(mx1 Int)(r node)(m4 Int)(mx2 Int))(and 
;lexvar(= n (+ (+ m4 1) m3))
(<= 0 d)
(<= mx1 d)
(<= mx2 d)
(<= d mx)
(= (+ m2 m4) m3)
(<= 0 m2)
(<= m2 1)
(= m m3)
(= m1 m4)
(= tprm t)
(< 0 n)
(tobool (ssep 
(pq l m mx1)
(pto tprm (sref (ref val d) (ref nleft m3) (ref nright m4) (ref left l) (ref right r) ))
(pq r m1 mx2)
) )
))
)

(assert (not 
(and 
(tobool  
(pto tprm (sref (ref val valprm) (ref nleft nleftprm) (ref nright nrightprm) (ref left leftprm) (ref right rightprm) ))
 )
)
))

(check-sat)