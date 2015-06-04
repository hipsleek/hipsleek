(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node2 0)
(declare-fun val () (Field node2 Int))
(declare-fun left () (Field node2 node2))
(declare-fun right () (Field node2 node2))

(define-fun complete ((?in node2) (?n Int) (?nmin Int))
Space (tospace
(or
(or
(and 
(= ?in nil)
(= ?n 0)
(= ?nmin 0)

)(exists ((?flted_25_33 Int)(?flted_25_34 Int))(and 
(= (+ ?flted_25_34 1) ?n)
(= (+ ?flted_25_33 2) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref left ?l) (ref right ?r) ))
(complete ?l ?flted_25_34 ?nmin1)
(complete ?r ?flted_25_33 ?nmin2)
) )
)))(exists ((?flted_26_35 Int)(?flted_26_36 Int))(and 
(= (+ ?flted_26_36 1) ?n)
(= (+ ?flted_26_35 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref left ?l) (ref right ?r) ))
(complete ?l ?flted_26_36 ?nmin1)
(complete ?r ?flted_26_35 ?nmin2)
) )
)))))









































































































































































(declare-fun Anon13 () Int)
(declare-fun l13 () node2)
(declare-fun auxprm () node2)
(declare-fun nmin66_8595 () Int)
(declare-fun flted30_8594 () Int)
(declare-fun nmin65 () Int)
(declare-fun n27 () Int)
(declare-fun nmin63 () Int)
(declare-fun n25 () Int)
(declare-fun nmin62 () Int)
(declare-fun n24 () NUM)
(declare-fun tmpprm () node2)
(declare-fun r13 () node2)
(declare-fun nmin61 () Int)
(declare-fun n22 () NUM)
(declare-fun nmin59 () Int)
(declare-fun n20 () NUM)
(declare-fun t () node2)
(declare-fun v20prm () node2)
(declare-fun v () node2)
(declare-fun tprm () node2)
(declare-fun nmin () Int)
(declare-fun nmin56 () Int)
(declare-fun nmin57 () Int)
(declare-fun flted28 () NUM)
(declare-fun flted29 () NUM)
(declare-fun n () Int)
(declare-fun n21 () NUM)
(declare-fun nmin58 () Int)
(declare-fun n23 () NUM)
(declare-fun nmin60 () Int)


(assert 
(exists ((flted30 Int)(nmin66 Int))(and 
;lexvar(<= nmin65 n27)
(<= 0 nmin65)
(= flted30 (+ 1 n27))
(<= nmin62 n24)
(<= 0 nmin62)
(= nmin65 nmin62)
(= n27 n24)
(<= nmin63 n25)
(<= 0 nmin63)
(<= nmin61 n23)
(<= 0 nmin61)
(= nmin63 nmin61)
(= n25 n23)
(= n25 n24)
(<= nmin59 n21)
(<= 0 nmin59)
(= nmin62 nmin59)
(= n24 n21)
(= tmpprm r13)
(<= nmin60 n22)
(<= 0 nmin60)
(= nmin61 nmin60)
(= n23 n22)
(<= nmin57 flted28)
(<= 0 nmin57)
(= nmin60 nmin57)
(= n22 flted28)
(<= nmin58 n20)
(<= 0 nmin58)
(= nmin59 nmin58)
(= n21 n20)
(<= nmin56 flted29)
(<= 0 nmin56)
(= nmin58 nmin56)
(= n20 flted29)
(= tprm t)
(= v20prm v)
(= nmin n)
(distinct tprm nil)
(= (+ flted28 1) n)
(= (+ flted29 1) n)
(<= n21 nmin58)
(<= n23 nmin60)
(tobool (ssep 
(pto tprm (sref (ref val Anon13) (ref left l13) (ref right r13) ))
(complete r13 n25 nmin63)
(complete auxprm flted30 nmin66)
) )
))
)

(assert (not 
(and 
(tobool  
(pto tprm (sref (ref val val18prm) (ref left left18prm) (ref right right18prm) ))
 )
)
))

(check-sat)