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























































































































(declare-fun p14_3676 () node2)
(declare-fun q19_3677 () node2)
(declare-fun x () node2)
(declare-fun aprm () node2)
(declare-fun a () node2)
(declare-fun tmp1prm () node2)
(declare-fun xprm () node2)
(declare-fun lg7_3672 () Int)
(declare-fun lg () Int)
(declare-fun sm7_3671 () Int)
(declare-fun sm () Int)
(declare-fun qs4_3674 () Int)
(declare-fun pl4_3673 () Int)
(declare-fun v6_3675 () Int)


(assert 
(exists ((sm7 Int)(lg7 Int)(pl4 Int)(qs4 Int)(v6 Int)(p14 node2)(q19 node2))(and 
;lexvar(= xprm x)
(= aprm a)
(= tmp1prm nil)
(distinct xprm nil)
(= lg7 lg)
(= sm7 sm)
(<= v6 qs4)
(<= pl4 v6)
(tobool (ssep 
(bst p14 sm7 pl4)
(pto xprm (sref (ref val v6) (ref left p14) (ref right q19) ))
(bst q19 qs4 lg7)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val15prm) (ref left left15prm) (ref right right15prm) ))
 )
)
))

(check-sat)