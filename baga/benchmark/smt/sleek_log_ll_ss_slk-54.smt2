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

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_14_23 Int))(and 
(= (+ ?flted_14_23 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q ?flted_14_23)
) )
)))))
















































































































































































































































(declare-fun Anon17 () Int)
(declare-fun tmpprm () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun flted26 () Int)
(declare-fun n () Int)
(declare-fun q17 () node)
(declare-fun v22prm () node)


(assert 
(and 
;lexvar(= tmpprm nil)
(< 0 n)
(= aprm a)
(= xprm x)
(= (+ flted26 1) n)
(= v22prm q17)
(distinct v22prm nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon17) (ref next q17) ))
(ll q17 flted26)
) )
)
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)