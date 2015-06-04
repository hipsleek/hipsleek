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
















































































































































































































































(declare-fun Anon11 () Int)
(declare-fun v19prm () node)
(declare-fun tmpprm () node)
(declare-fun q11 () node)
(declare-fun flted17 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= v19prm nil)
(= tmpprm q11)
(= (+ flted17 1) n)
(= xprm x)
(< 0 n)
(tobool (ssep 
(pto xprm (sref (ref val Anon11) (ref next q11) ))
(ll q11 flted17)
) )
)
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val11prm) (ref next next11prm) ))
 )
)
))

(check-sat)