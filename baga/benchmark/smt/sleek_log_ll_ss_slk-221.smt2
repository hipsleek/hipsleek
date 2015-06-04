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
(declare-fun q65 () node)
(declare-fun Anon65 () node)
(declare-fun Anon64 () node)
(declare-fun ys16 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next20 () node)
(declare-fun q64 () node)
(declare-fun xs16 () node)
(declare-fun flted90 () Int)
(declare-fun flted91_5107 () Int)
(declare-fun n23 () Int)
(declare-fun m16 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted91 Int))(and 
;lexvar(= (+ m 1) m16)
(= q65 ys16)
(= Anon65 Anon64)
(= (+ flted90 1) n)
(= ys16 ys)
(= xs16 xs)
(= next20 q64)
(= n23 flted90)
(<= 0 m)
(distinct xs16 nil)
(<= 0 flted90)
(= flted91 (+ m16 n23))
(= xsprm nil)
(<= 0 n23)
(<= 0 m16)
(tobool  
(ll ysprm flted91)
 )
))
)

(assert (not 
(exists ((flted92 Int))(and 
(= xsprm nil)
(= flted92 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted92)
 )
))
))

(check-sat)