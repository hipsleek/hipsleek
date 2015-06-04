(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
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

(define-fun bst ((?in node2) (?sm NUM) (?lg NUM))
Space (tospace
(or
(and 
(= ?in nil)
(<= ?sm ?lg)

)(exists ((?sm_37 Int)(?lg_38 Int)(?pl_35 Int)(?qs_36 Int))(and 
(<= ?pl_35 ?v)
(<= ?v ?qs_36)
(= ?sm_37 ?sm)
(= ?lg_38 ?lg)
(tobool (ssep 
(pto ?in (sref (ref val ?v) (ref left ?p) (ref right ?q) ))
(bst ?p ?sm_37 ?pl_35)
(bst ?q ?qs_36 ?lg_38)
) )
)))))

(define-fun tree1 ((?in node2) (?m Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?m 0)

)(and 
(= ?m (+ (+ ?m2 1) ?m1))
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref left ?p) (ref right ?q) ))
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
(pto ?in (sref (ref val ?Anon_15) (ref left ?p) (ref right ?q) ))
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

)(exists ((?p_39 node2)(?self_40 node2))(and 
(= ?n (+ 1 ?n1))
(= ?p_39 ?p)
(= ?self_40 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_16) (ref left ?p_39) (ref right ?q) ))
(dll ?q ?self_40 ?n1)
) )
)))))























































































































(declare-fun r4 () node2)
(declare-fun Anon11 () Int)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun m12 () Int)
(declare-fun n8 () Int)
(declare-fun n10 () Int)
(declare-fun m11 () Int)
(declare-fun n9 () Int)
(declare-fun n11 () Int)
(declare-fun Anon () node2)
(declare-fun q13 () node2)
(declare-fun Anon1 () node2)
(declare-fun q15 () node2)
(declare-fun m14 () Int)
(declare-fun m13 () Int)
(declare-fun flted4 () Int)
(declare-fun m15 () Int)
(declare-fun n12 () Int)
(declare-fun v5 () node2)
(declare-fun left1 () node2)
(declare-fun p11 () node2)
(declare-fun right1 () node2)
(declare-fun q11 () node2)
(declare-fun tmpprm () node2)


(assert 
(and 
;lexvar(= m (+ (+ m11 1) m12))
(distinct xprm nil)
(= xprm x)
(= m13 m12)
(= n10 n8)
(<= 0 m12)
(<= 0 n8)
(= q13 nil)
(<= 0 n10)
(= m14 m11)
(= n11 n9)
(<= 0 m11)
(<= 0 n9)
(= q15 nil)
(<= 0 n11)
(= Anon q13)
(= m15 m13)
(= Anon1 q15)
(= n12 m14)
(<= 0 m14)
(<= 0 m13)
(= flted4 (+ n12 m15))
(<= 0 m15)
(<= 0 n12)
(= v5 nil)
(= left1 p11)
(= right1 q11)
(distinct tmpprm nil)
(tobool (ssep 
(dll tmpprm r4 flted4)
(pto xprm (sref (ref val Anon11) (ref left v5) (ref right tmpprm) ))
) )
)
)

(assert (not 
;lexvar
))

(check-sat)