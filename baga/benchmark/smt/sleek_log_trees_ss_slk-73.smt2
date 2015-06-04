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























































































































(declare-fun p9 () node2)
(declare-fun xright_2181 () node2)
(declare-fun q9 () node2)
(declare-fun pl3 () Int)
(declare-fun sm4 () Int)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun xval () Int)
(declare-fun v3 () Int)
(declare-fun qs3 () Int)
(declare-fun lg4 () Int)
(declare-fun tmp_2182 () Int)
(declare-fun s4_2180 () Int)
(declare-fun s () Int)
(declare-fun b () Int)
(declare-fun sm () Int)
(declare-fun lg () Int)


(assert 
(exists ((s4 Int)(xrightprm node2)(tmpprm Int))(and 
;lexvar(distinct q9 nil)
(= xval aprm)
(<= pl3 v3)
(<= v3 qs3)
(= sm4 sm)
(= lg4 lg)
(distinct xprm nil)
(= aprm a)
(= xprm x)
(= xval v3)
(= s qs3)
(= b lg4)
(<= qs3 lg4)
(<= s tmpprm)
(<= tmpprm s4)
(<= s b)
(tobool (ssep 
(bst p9 sm4 pl3)
(bst xrightprm s4 b)
(pto xprm (sref (ref val tmpprm) (ref left p9) (ref right xrightprm) ))
) )
))
)

(assert (not 
(exists ((s5 Int)(l Int))(and 
(<= l lg)
(<= sm s5)
(<= sm lg)
(tobool  
(bst xprm s5 l)
 )
))
))

(check-sat)