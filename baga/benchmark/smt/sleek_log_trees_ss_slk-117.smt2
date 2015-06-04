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























































































































(declare-fun q20 () node2)
(declare-fun left3 () node2)
(declare-fun p15 () node2)
(declare-fun ma3 () Int)
(declare-fun mi3 () Int)
(declare-fun v26_4116 () node2)
(declare-fun lg9 () Int)
(declare-fun sm9 () Int)
(declare-fun x () node2)
(declare-fun xprm () node2)
(declare-fun lg8 () Int)
(declare-fun sm8 () NUM)
(declare-fun qs5 () Int)
(declare-fun pl5 () NUM)
(declare-fun aprm () Int)
(declare-fun v7 () Int)
(declare-fun a () Int)
(declare-fun res () node2)
(declare-fun sm () Int)
(declare-fun lg () Int)


(assert 
(exists ((v26prm node2))(and 
;lexvar(= res xprm)
(= left3 p15)
(<= sm9 lg9)
;eqmax;eqmin(distinct v26prm nil)
(<= sm8 pl5)
(= lg9 pl5)
(= sm9 sm8)
(= xprm x)
(= aprm a)
(distinct xprm nil)
(= lg8 lg)
(= sm8 sm)
(<= v7 qs5)
(<= pl5 v7)
(<= aprm v7)
(tobool (ssep 
(bst q20 qs5 lg8)
(bst v26prm mi3 ma3)
(pto xprm (sref (ref val v7) (ref left v26prm) (ref right q20) ))
) )
))
)

(assert (not 
(exists ((mi2 Int)(ma2 Int))(and 
;eqmax;eqmin(distinct res nil)
(<= sm lg)
(tobool  
(bst res mi2 ma2)
 )
))
))

(check-sat)