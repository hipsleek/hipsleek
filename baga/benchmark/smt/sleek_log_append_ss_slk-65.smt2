(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun lseg ((?in node) (?p node) (?n Int))
Space (tospace
(or
(and 
(= ?in ?p)
(= ?n 0)

)(exists ((?p_29 node)(?flted_11_28 Int))(and 
(= (+ ?flted_11_28 1) ?n)
(= ?p_29 ?p)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref next ?q) ))
(lseg ?q ?p_29 ?flted_11_28)
) )
)))))

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_7_31 Int))(and 
(= (+ ?flted_7_31 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q ?flted_7_31)
) )
)))))

(define-fun clist ((?in node) (?n Int))
Space (tospace
(exists ((?self_26 node)(?flted_14_25 Int))(and 
(= (+ ?flted_14_25 1) ?n)
(= ?self_26 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref next ?p) ))
(lseg ?p ?self_26 ?flted_14_25)
) )
))))



































































(declare-fun Anon7 () Int)
(declare-fun q7 () node)
(declare-fun flted10 () node)
(declare-fun yprm () node)
(declare-fun xprm () node)
(declare-fun r1 () node)
(declare-fun p2 () node)
(declare-fun b1 () Int)
(declare-fun flted11 () Int)
(declare-fun n18 () Int)
(declare-fun x () node)
(declare-fun y () node)
(declare-fun b () Int)
(declare-fun r () node)
(declare-fun n () Int)


(assert 
(exists ((flprm boolean))(and 
;lexvar(distinct q7 nil)
(= flted10 nil)
(= yprm y)
(= xprm x)
(= p2 r)
(= (+ flted11 1) n)
(= r1 p2)
(= n18 flted11)
(= b1 b)
(distinct r nil)
(<= 0 flted11)
(<= 0 n18)
(tobool (ssep 
(pto xprm (sref (ref val Anon7) (ref next q7) ))
(lseg q7 r1 n18)
(pto r1 (sref (ref val b1) (ref next yprm) ))
) )
))
)

(assert (not 
(exists ((r2 node)(n19 Int)(b2 Int)(y2 node))(and 
(= y2 y)
(= b2 b)
(= n19 n)
(= r2 r)
(<= 0 n)
(tobool (ssep 
(lseg x r2 n19)
(pto r (sref (ref val b2) (ref next y2) ))
) )
))
))

(check-sat)