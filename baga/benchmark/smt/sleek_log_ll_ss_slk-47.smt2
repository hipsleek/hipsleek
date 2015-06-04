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
(declare-fun next3 () node)
(declare-fun q11 () node)
(declare-fun v19_1066 () node)
(declare-fun flted17 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun res () node)
(declare-fun n () Int)


(assert 
(exists ((v19prm node))(and 
;lexvar(= res q11)
(= next3 q11)
(= v19prm nil)
(= (+ flted17 1) n)
(= xprm x)
(< 0 n)
(tobool (ssep 
(ll q11 flted17)
(pto xprm (sref (ref val Anon11) (ref next v19prm) ))
) )
))
)

(assert (not 
(exists ((flted18 Int)(flted19 Int))(and 
(= (+ flted18 1) n)
(= flted19 1)
(<= 0 n)
(tobool (ssep 
(ll x flted19)
(ll res flted18)
) )
))
))

(check-sat)