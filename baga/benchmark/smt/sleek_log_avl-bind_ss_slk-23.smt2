(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun height () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun avl ((?in node) (?m Int) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?m 0)
(= ?n 0)

)(exists ((?n_33 Int))(and 
(= ?m (+ (+ ?m2 1) ?m1))
(<= (+ 0 ?n2) (+ ?n1 1))
(<= ?n1 (+ 1 ?n2))
(= ?n_33 ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref height ?n_33) (ref left ?p) (ref right ?q) ))
(avl ?p ?m1 ?n1)
(avl ?q ?m2 ?n2)
) )
)))))











































































































































































(declare-fun v8prm () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun res () Int)
(declare-fun n () Int)
(declare-fun m () Int)


(assert 
(and 
;lexvar(= res v8prm)
(= v8prm 0)
(= xprm x)
(= xprm nil)
(tobool  
(avl x m n)
 )
)
)

(assert (not 
(exists ((m11 Int)(n16 Int))(and 
(= n16 n)
(= m11 m)
(= res n)
(<= 0 n)
(<= 0 m)
(tobool  
(avl x m11 n16)
 )
))
))

(check-sat)