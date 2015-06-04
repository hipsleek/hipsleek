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
(declare-fun v23prm () node)
(declare-fun flted26 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun n () Int)
(declare-fun tmpprm () node)
(declare-fun q17 () node)


(assert 
(and 
;lexvar(= (+ flted26 1) n)
(= xprm x)
(= aprm a)
(< 0 n)
(= tmpprm nil)
(= q17 nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon17) (ref next q17) ))
(ll q17 flted26)
(pto v23prm (sref (ref val aprm) (ref next tmpprm) ))
) )
)
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val15prm) (ref next next15prm) ))
 )
)
))

(check-sat)