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































































(declare-fun Anon9 () Int)
(declare-fun p5 () node2)
(declare-fun m7 () Int)
(declare-fun v5prm () node2)
(declare-fun q5 () node2)
(declare-fun cleftprm () Int)
(declare-fun m6 () Int)
(declare-fun z () node2)
(declare-fun zprm () node2)
(declare-fun m () Int)
(declare-fun m5 () Int)
(declare-fun m4 () Int)


(assert 
(and 
;lexvar(= m7 m4)
(= v5prm q5)
(<= 0 m6)
(<= 0 cleftprm)
(= cleftprm m6)
(<= 0 m5)
(= m6 m5)
(= zprm z)
(distinct zprm nil)
(not )(= m (+ (+ m4 1) m5))
(tobool (ssep 
(pto zprm (sref (ref val Anon9) (ref left p5) (ref right q5) ))
(tree1 p5 m6)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)