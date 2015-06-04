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
































































































































































(declare-fun v12prm () Int)
(declare-fun m19_1778 () Int)
(declare-fun m18_1777 () Int)
(declare-fun mx2 () Int)
(declare-fun mx1 () Int)
(declare-fun rprm () node)
(declare-fun r2 () node)
(declare-fun lprm () node)
(declare-fun l2 () node)
(declare-fun m2prm () Int)
(declare-fun m2 () Int)
(declare-fun m1prm () Int)
(declare-fun m1 () Int)
(declare-fun v13prm () Int)
(declare-fun v12 () Int)
(declare-fun dprm () Int)
(declare-fun d2 () Int)


(assert 
(exists ((m18 Int)(m19 Int))(and 
;lexvar(distinct m1prm v12prm)
(= v12prm 0)
(= m19 m2)
(= m18 m1)
(<= v12 d2)
(<= 0 v12)
(<= mx2 d2)
(<= mx1 d2)
(<= m1 (+ 1 m2))
(<= (+ 0 m2) m1)
(= rprm r2)
(= lprm l2)
(= m2prm m2)
(= m1prm m1)
(= v13prm v12)
(= dprm d2)
(tobool (ssep 
(pq l2 m18 mx1)
(pq r2 m19 mx2)
) )
))
)

(assert (not 
;lexvar
))

(check-sat)