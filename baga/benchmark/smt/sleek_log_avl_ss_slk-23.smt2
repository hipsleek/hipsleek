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

(define-fun avl ((?in node) (?size Int) (?height Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?size 0)
(= ?height 0)

)(exists ((?height_34 Int))(and 
(= ?size (+ (+ ?size2 1) ?size1))
(<= ?height2 (+ 1 ?height1))
(<= ?height1 (+ 1 ?height2))
(= ?height_34 ?height)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref height ?height_34) (ref left ?p) (ref right ?q) ))
(avl ?p ?size1 ?height1)
(avl ?q ?size2 ?height2)
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
(exists ((m1 Int)(n1 Int))(and 
(= n1 n)
(= m1 m)
(= res n)
(<= 0 n)
(<= 0 m)
(tobool  
(avl x m1 n1)
 )
))
))

(check-sat)