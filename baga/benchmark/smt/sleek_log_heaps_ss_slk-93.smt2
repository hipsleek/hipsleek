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
































































































































































(declare-fun trightprm () node)
(declare-fun r10 () node)
(declare-fun tleftprm () node)
(declare-fun l10 () node)
(declare-fun tvalprm () NUM)
(declare-fun tprm () node)
(declare-fun t () node)
(declare-fun m61 () Int)
(declare-fun m62 () Int)
(declare-fun m63 () Int)
(declare-fun mx () NUM)
(declare-fun mx38 () Int)
(declare-fun mx39 () Int)
(declare-fun d17 () Int)
(declare-fun n () Int)
(declare-fun m65 () Int)
(declare-fun m64 () Int)
(declare-fun tnleftprm () Int)
(declare-fun tnrightprm () Int)


(assert 
(and 
;lexvar(= trightprm r10)
(= tleftprm l10)
(= tnrightprm m64)
(= tnleftprm m65)
(= tvalprm d17)
(= m64 0)
(distinct m65 0)
(< 0 n)
(= tprm t)
(= m61 m64)
(= m62 m65)
(<= m63 1)
(<= 0 m63)
(= (+ m63 m64) m65)
(<= d17 mx)
(<= mx38 d17)
(<= mx39 d17)
(<= 0 d17)
(= n (+ (+ m64 1) m65))
(tobool (ssep 
(pq l10 m62 mx39)
(pq r10 m61 mx38)
) )
)
)

(assert (not 
(exists ((m10 Int)(m11 Int))(and 
(= m11 tnrightprm)
(= m10 tnleftprm)
(<= tnleftprm (+ 1 tnrightprm))
(<= (+ 0 tnrightprm) tnleftprm)
(< 0 (+ tnrightprm tnleftprm))
(tobool (ssep 
(pq tleftprm m10 mx1)
(pq trightprm m11 mx2)
) )
))
))

(check-sat)