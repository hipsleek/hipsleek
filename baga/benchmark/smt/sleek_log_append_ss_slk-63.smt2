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
(declare-fun b1 () node)
(declare-fun b () node)
(declare-fun n18 () Int)
(declare-fun r1 () node)
(declare-fun vprm () node)
(declare-fun q7 () node)
(declare-fun flted11 () Int)
(declare-fun n () Int)
(declare-fun p2 () node)
(declare-fun r () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun flted10 () node)
(declare-fun tmpprm () node)


(assert 
(and 
;lexvar(= b1 b)
(= n18 flted11)
(= r1 p2)
(= vprm q7)
(= tmpprm q7)
(= (+ flted11 1) n)
(= p2 r)
(= xprm x)
(= yprm y)
(= flted10 nil)
(distinct tmpprm nil)
(tobool  
(pto xprm (sref (ref val Anon7) (ref next q7) ))
 )
)
)

(assert (not 
;lexvar
))

(check-sat)