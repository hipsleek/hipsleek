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































































(declare-fun Anon3 () Int)
(declare-fun Anon1 () node2)
(declare-fun n () Int)
(declare-fun v1prm () node2)
(declare-fun q1 () node2)
(declare-fun x () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun self2 () node2)
(declare-fun xprm () node2)
(declare-fun p1 () node2)
(declare-fun Anon () node2)
(declare-fun m () Int)
(declare-fun n2 () Int)


(assert 
(and 
;lexvar(= v1prm q1)
(= xprm x)
(= yprm y)
(distinct xprm nil)
(not )(= self2 xprm)
(= p1 Anon)
(= m (+ 1 n2))
(tobool (ssep 
(pto xprm (sref (ref val Anon3) (ref left p1) (ref right q1) ))
(dll q1 self2 n2)
(dll y Anon1 n)
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(dll v1prm Anon4 m1)
(dll yprm Anon5 n3)
) )
)
))

(check-sat)