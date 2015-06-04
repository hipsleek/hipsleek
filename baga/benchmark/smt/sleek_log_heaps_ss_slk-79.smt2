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
































































































































































(declare-fun l9_6153 () node)
(declare-fun r9_6156 () node)
(declare-fun mx36_6155 () Int)
(declare-fun mx37_6158 () Int)
(declare-fun d16_6152 () Int)
(declare-fun mx () Int)
(declare-fun m58_6151 () Int)
(declare-fun m56_6149 () Int)
(declare-fun m59_6154 () Int)
(declare-fun m57_6150 () Int)
(declare-fun m60_6157 () Int)
(declare-fun tprm () node)
(declare-fun t () node)
(declare-fun n () Int)


(assert 
(exists ((m56 Int)(m57 Int)(m58 Int)(d16 Int)(l9 node)(m59 Int)(mx36 Int)(r9 node)(m60 Int)(mx37 Int))(and 
;lexvar(= n (+ (+ m60 1) m59))
(<= 0 d16)
(<= mx36 d16)
(<= mx37 d16)
(<= d16 mx)
(= (+ m58 m60) m59)
(<= 0 m58)
(<= m58 1)
(= m56 m59)
(= m57 m60)
(= tprm t)
(< 0 n)
(tobool (ssep 
(pq l9 m56 mx36)
(pto tprm (sref (ref val d16) (ref nleft m59) (ref nright m60) (ref left l9) (ref right r9) ))
(pq r9 m57 mx37)
) )
))
)

(assert (not 
(and 
(tobool  
(pto tprm (sref (ref val val22prm) (ref nleft nleft22prm) (ref nright nright22prm) (ref left left22prm) (ref right right22prm) ))
 )
)
))

(check-sat)