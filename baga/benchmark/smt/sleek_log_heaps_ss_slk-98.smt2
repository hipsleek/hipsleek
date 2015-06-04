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
































































































































































(declare-fun tmpprm () Int)
(declare-fun v13prm () Int)
(declare-fun maxi4 () NUM)
(declare-fun mx44 () Int)
(declare-fun mx38 () Int)
(declare-fun mx () Int)
(declare-fun m63 () Int)
(declare-fun m62 () Int)
(declare-fun tprm () __Exc)
(declare-fun t () __Exc)
(declare-fun n () Int)
(declare-fun m65 () Int)
(declare-fun m64 () Int)
(declare-fun tvalprm () Int)
(declare-fun d17 () Int)
(declare-fun mx1 () Int)
(declare-fun mx39 () Int)
(declare-fun m61 () Int)
(declare-fun r10 () __Exc)
(declare-fun mx2 () Int)
(declare-fun mx45 () Int)
(declare-fun tnleftprm () Int)
(declare-fun tleftprm () __Exc)
(declare-fun tnrightprm () Int)
(declare-fun trightprm () __Exc)
(declare-fun mx41 () Int)
(declare-fun mx40 () Int)


(assert 
(and 
;lexvar(= trightprm nil)
(= tnrightprm 0)
(= mx44 0)
(= tmpprm tvalprm)
(<= 0 mx2)
(<= 0 mx1)
(<= v13prm maxi4)
(<= 0 v13prm)
;eqmax(<= mx44 mx2)
(<= mx45 mx1)
(<= tnleftprm (+ 1 tnrightprm))
(<= (+ 0 tnrightprm) tnleftprm)
(= (+ (+ 1 tnleftprm) tnrightprm) (+ m64 m65))
(<= 0 mx39)
(<= 0 m62)
(= r10 nil)
(= m61 0)
(= mx38 0)
(= n (+ (+ m64 1) m65))
(<= 0 d17)
(<= mx39 d17)
(<= mx38 d17)
(<= d17 mx)
(= (+ m63 m64) m65)
(<= 0 m63)
(<= m63 1)
(= m62 m65)
(= m61 m64)
(= tprm t)
(< 0 n)
(distinct m65 0)
(= m64 0)
(= tvalprm d17)
(= mx1 mx39)
(= mx2 0)
(= mx45 0)
(= tnleftprm 0)
(= tleftprm nil)
(= mx41 0)
(= mx40 0)

)
)

(assert (not 
;lexvar
))

(check-sat)