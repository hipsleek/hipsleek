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


















































































































































































































(declare-fun Anon73_5011 () Int)
(declare-fun q73_5012 () node)
(declare-fun v46prm () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun flted103_5010 () Int)
(declare-fun i () Int)


(assert 
(exists ((flted103 Int)(Anon73 Int)(q73 node))(and 
;lexvar(= v46prm nil)
(= xprm x)
(< 0 i)
(< 3 4)
(= (+ flted103 1) i)
(tobool (ssep 
(pto xprm (sref (ref val Anon73) (ref next q73) ))
(ll q73 flted103)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val53prm) (ref next next53prm) ))
 )
)
))

(check-sat)