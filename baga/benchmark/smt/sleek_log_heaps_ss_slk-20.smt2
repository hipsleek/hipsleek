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
































































































































































(declare-fun mx2 () NUM)
(declare-fun mx1 () NUM)
(declare-fun trightprm () __Exc)
(declare-fun r1 () __Exc)
(declare-fun tleftprm () __Exc)
(declare-fun l1 () __Exc)
(declare-fun tnrightprm () Int)
(declare-fun tnleftprm () Int)
(declare-fun tvalprm () NUM)
(declare-fun tprm () __Exc)
(declare-fun t () __Exc)
(declare-fun m5 () Int)
(declare-fun m6 () Int)
(declare-fun m7 () Int)
(declare-fun mx () NUM)
(declare-fun mx3 () NUM)
(declare-fun mx4 () NUM)
(declare-fun d1 () Int)
(declare-fun n () Int)
(declare-fun m9 () Int)
(declare-fun m8 () Int)


(assert 
(and 
;lexvar(= mx2 mx3)
(= mx1 mx4)
(= trightprm r1)
(= tleftprm l1)
(= tnrightprm m8)
(= tnleftprm m9)
(= tvalprm d1)
(distinct m9 0)
(< 0 n)
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
(distinct m8 0)

)
)

(assert (not 
;lexvar
))

(check-sat)