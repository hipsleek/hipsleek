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
(declare-fun n12 () Int)
(declare-fun Anon1 () node2)
(declare-fun m15 () Int)
(declare-fun Anon () node2)
(declare-fun v14prm () node2)
(declare-fun q7 () node2)
(declare-fun v13prm () node2)
(declare-fun p7 () node2)
(declare-fun q11 () node2)
(declare-fun n11 () Int)
(declare-fun m14 () Int)
(declare-fun q9 () node2)
(declare-fun n10 () Int)
(declare-fun m13 () Int)
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
;lexvar(= n12 m14)
(= Anon1 q11)
(= m15 m13)
(= Anon q9)
(= v14prm q7)
(= v13prm p7)
(<= 0 n11)
(<= 0 m14)
(= q11 nil)
(<= 0 n9)
(<= 0 m11)
(= n11 n9)
(= m14 m11)
(<= 0 n10)
(<= 0 m13)
(= q9 nil)
(<= 0 n8)
(<= 0 m12)
(= n10 n8)
(= m13 m12)
(= xprm x)
(distinct xprm nil)
(= m (+ (+ m11 1) m12))
(tobool  
(pto xprm (sref (ref val Anon11) (ref left p7) (ref right q7) ))
 )
)
)

(assert (not 
;lexvar
))

(check-sat)