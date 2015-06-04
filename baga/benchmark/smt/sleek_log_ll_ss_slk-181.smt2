(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_14_23 Int))(and 
(= (+ ?flted_14_23 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q ?flted_14_23)
) )
)))))
















































































































































































































































(declare-fun ysprm () node)
(declare-fun q53 () node)
(declare-fun Anon53 () node)
(declare-fun Anon52 () node)
(declare-fun ys12 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next16 () node)
(declare-fun q52 () node)
(declare-fun xs12 () node)
(declare-fun flted74 () Int)
(declare-fun flted75_4183 () Int)
(declare-fun n19 () Int)
(declare-fun m12 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted75 Int))(and 
;lexvar(= (+ m 1) m12)
(= q53 ys12)
(= Anon53 Anon52)
(= (+ flted74 1) n)
(= ys12 ys)
(= xs12 xs)
(= next16 q52)
(= n19 flted74)
(<= 0 m)
(distinct xs12 nil)
(<= 0 flted74)
(= flted75 (+ m12 n19))
(= xsprm nil)
(<= 0 n19)
(<= 0 m12)
(tobool  
(ll ysprm flted75)
 )
))
)

(assert (not 
(exists ((flted76 Int))(and 
(= xsprm nil)
(= flted76 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted76)
 )
))
))

(check-sat)