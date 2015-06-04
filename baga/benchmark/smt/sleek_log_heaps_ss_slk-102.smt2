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
































































































































































(declare-fun tval_7401 () Int)
(declare-fun max7_7398 () Int)
(declare-fun max6_7397 () Int)
(declare-fun mx52_7400 () Int)
(declare-fun mx51_7399 () Int)
(declare-fun v25_7406 () Int)
(declare-fun maxi4 () Int)
(declare-fun mx44 () Int)
(declare-fun mx38 () Int)
(declare-fun d17 () Int)
(declare-fun m63 () Int)
(declare-fun m62 () Int)
(declare-fun tprm () node)
(declare-fun t () node)
(declare-fun m65 () Int)
(declare-fun m64 () Int)
(declare-fun mx1 () Int)
(declare-fun mx39 () Int)
(declare-fun m61 () Int)
(declare-fun r10 () node)
(declare-fun mx2 () Int)
(declare-fun mx45 () Int)
(declare-fun tnleft_7402 () Int)
(declare-fun tleft_7404 () node)
(declare-fun tnright_7403 () Int)
(declare-fun tright_7405 () node)
(declare-fun mx41 () Int)
(declare-fun mx40 () Int)
(declare-fun res () Int)
(declare-fun mx () Int)
(declare-fun n () Int)


(assert 
(exists ((max6 Int)(max7 Int)(mx51 Int)(mx52 Int)(tval Int)(tnleft Int)(tnright Int)(tleft node)(tright node)(v25 Int))(and 
;lexvar(= mx51 0)
(= mx52 0)
(= res d17)
(<= 0 mx40)
(<= 0 mx41)
(<= 0 tval)
(<= mx52 tval)
(<= mx51 tval)
(<= tval max7)
;eqmax;eqmax(<= mx52 mx40)
(<= mx51 mx41)
(= tright nil)
(= tnright 0)
(= mx44 0)
(<= 0 mx2)
(<= 0 mx1)
(<= v25 maxi4)
(<= 0 v25)
;eqmax(<= mx44 mx2)
(<= mx45 mx1)
(<= tnleft (+ 1 tnright))
(<= (+ 0 tnright) tnleft)
(= (+ (+ 1 tnleft) tnright) (+ m64 m65))
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
(= mx1 mx39)
(= mx2 0)
(= mx45 0)
(= tnleft 0)
(= tleft nil)
(= mx41 0)
(= mx40 0)
(tobool  
(pto tprm (sref (ref val tval) (ref nleft tnleft) (ref nright tnright) (ref left tleft) (ref right tright) ))
 )
))
)

(assert (not 
(exists ((flted3 Int)(mx50 Int))(and 
(<= res mx)
(<= mx50 res)
(= (+ flted3 1) n)
(<= 0 mx)
(<= 0 n)
(tobool  
(pq tprm flted3 mx50)
 )
))
))

(check-sat)