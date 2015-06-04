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
































































































































































(declare-fun d12 () Int)
(declare-fun v13prm () Int)
(declare-fun m2prm () Int)
(declare-fun lprm () node)
(declare-fun rprm () node)
(declare-fun d2 () Int)
(declare-fun m21 () Int)
(declare-fun m20 () Int)
(declare-fun m1prm () Int)
(declare-fun l2 () node)
(declare-fun r2 () node)
(declare-fun m2 () Int)
(declare-fun m1 () Int)
(declare-fun dprm () Int)
(declare-fun v12 () Int)
(declare-fun mx2 () Int)
(declare-fun mx1 () Int)


(assert 
(and 
;lexvar(= dprm v13prm)
(= m2prm 0)
(= d12 d2)
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
(= m21 m1)
(= m20 m2)
(= m1prm 0)
(tobool (ssep 
(pq l2 m21 mx1)
(pq r2 m20 mx2)
) )
)
)

(assert (not 
(exists ((m54 Int)(m55 Int)(maxx Int)(max1 Int)(mx30 Int)(mx31 Int))(and 
(= m55 m2)
(= m54 m1)
(<= 0 dprm)
(<= mx31 dprm)
(<= mx30 dprm)
(<= dprm max1)
;eqmax;eqmax(<= mx31 mx2)
(<= mx30 mx1)
(<= 0 mx2)
(<= 0 mx1)
(tobool (ssep 
(pq l2 m54 mx30)
(pq r2 m55 mx31)
) )
))
))

(check-sat)