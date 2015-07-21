(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/hip/
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

)(exists ((?flted_14_24 Int))(and 
(= (+ ?flted_14_24 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref next ?q) ))
(ll ?q ?flted_14_24)
) )
)))))


















































































































































































































(declare-fun Anon17 () Int)
(declare-fun v25prm () node)
(declare-fun flted26 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun n () Int)
(declare-fun tmpprm () node)
(declare-fun q17 () node)


(assert 
(and 
;lexvar(= v25prm q17)
(= (+ flted26 1) n)
(= xprm x)
(= aprm a)
(< 0 n)
(= tmpprm nil)
(distinct q17 nil)
(not )(tobool (ssep 
(pto xprm (sref (ref val Anon17) (ref next q17) ))
(ll q17 flted26)
) )
)
)

(assert (not 
(and 
(< 0 n6)
(tobool  
(ll v25prm n6)
 )
)
))

(check-sat)