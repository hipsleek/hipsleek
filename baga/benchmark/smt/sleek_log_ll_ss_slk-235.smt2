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
















































































































































































































































(declare-fun Anon71_5463 () Int)
(declare-fun q71_5464 () node)
(declare-fun flted100_5462 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun i () Int)
(declare-fun v43prm () node)


(assert 
(exists ((flted100 Int)(Anon71 Int)(q71 node))(and 
;lexvar(= (+ flted100 1) i)
(= xprm x)
(< 0 i)
(= v43prm nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon71) (ref next q71) ))
(ll q71 flted100)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val52prm) (ref next next52prm) ))
 )
)
))

(check-sat)