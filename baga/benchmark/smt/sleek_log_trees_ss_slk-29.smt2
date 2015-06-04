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























































































































(declare-fun Anon8_874 () Int)
(declare-fun p4_875 () node2)
(declare-fun q4_877 () node2)
(declare-fun z () node2)
(declare-fun zprm () node2)
(declare-fun m () Int)
(declare-fun m2_876 () Int)
(declare-fun m3_878 () Int)


(assert 
(exists ((Anon8 Int)(p4 node2)(m2 Int)(q4 node2)(m3 Int))(and 
;lexvar(= zprm z)
(distinct zprm nil)
(= m (+ (+ m3 1) m2))
(tobool (ssep 
(pto zprm (sref (ref val Anon8) (ref left p4) (ref right q4) ))
(tree1 p4 m2)
(tree1 q4 m3)
) )
))
)

(assert (not 
(and 
(tobool  
(pto zprm (sref (ref val val3prm) (ref left left3prm) (ref right right3prm) ))
 )
)
))

(check-sat)