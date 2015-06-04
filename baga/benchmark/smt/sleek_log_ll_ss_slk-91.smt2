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
(declare-fun q26 () node)
(declare-fun Anon26 () node)
(declare-fun Anon25 () node)
(declare-fun ys3 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next7 () node)
(declare-fun q25 () node)
(declare-fun xs3 () node)
(declare-fun flted38 () Int)
(declare-fun flted39_2104 () Int)
(declare-fun n10 () Int)
(declare-fun m3 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted39 Int))(and 
;lexvar(= (+ m 1) m3)
(= q26 ys3)
(= Anon26 Anon25)
(= (+ flted38 1) n)
(= ys3 ys)
(= xs3 xs)
(= next7 q25)
(= n10 flted38)
(<= 0 m)
(distinct xs3 nil)
(<= 0 flted38)
(= flted39 (+ m3 n10))
(= xsprm nil)
(<= 0 n10)
(<= 0 m3)
(tobool  
(ll ysprm flted39)
 )
))
)

(assert (not 
(exists ((flted40 Int))(and 
(= xsprm nil)
(= flted40 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted40)
 )
))
))

(check-sat)