(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/hip/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node2 0)
(declare-fun val () (Field node2 Int))
(declare-fun left () (Field node2 node2))
(declare-fun right () (Field node2 node2))

(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun tree1 ((?in node2) (?m Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?m 0)

)(and 
(= ?m (+ (+ ?m2 1) ?m1))
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_15) (ref left ?p) (ref right ?q) ))
(tree1 ?p ?m1)
(tree1 ?q ?m2)
) )
))))

(define-fun tree ((?in node2) (?m Int) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?m 0)
(= ?n 0)

)(and 
(= ?m (+ (+ ?m2 1) ?m1))
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_16) (ref left ?p) (ref right ?q) ))
(tree ?p ?m1 ?n1)
(tree ?q ?m2 ?n2)
) )
))))

(define-fun dll ((?in node2) (?p node2) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?p_33 node2)(?self_34 node2))(and 
(= ?n (+ 1 ?n1))
(= ?p_33 ?p)
(= ?self_34 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_17) (ref left ?p_33) (ref right ?q) ))
(dll ?q ?self_34 ?n1)
) )
)))))































































(declare-fun Anon11 () Int)
(declare-fun q7 () node2)
(declare-fun v11prm () node2)
(declare-fun p7 () node2)
(declare-fun x () node2)
(declare-fun xprm () node2)
(declare-fun n () Int)
(declare-fun n8 () Int)
(declare-fun n9 () Int)
(declare-fun m () Int)
(declare-fun m12 () Int)
(declare-fun m11 () Int)


(assert 
(and 
;lexvar(= v11prm p7)
(= xprm x)
(distinct xprm nil)
(= m (+ (+ m11 1) m12))
(tobool (ssep 
(pto xprm (sref (ref val Anon11) (ref left p7) (ref right q7) ))
(tree p7 m12 n8)
(tree q7 m11 n9)
) )
)
)

(assert (not 
(and 
(tobool  
(tree v11prm m13 n10)
 )
)
))

(check-sat)