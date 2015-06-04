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
















































































































































































































































(declare-fun v9prm () node)
(declare-fun aprm () Int)
(declare-fun res () node)
(declare-fun a () Int)


(assert 
(and 
;lexvar(= res v9prm)
(= v9prm nil)
(= aprm a)
(<= 0 a)
(= aprm 0)

)
)

(assert (not 
(exists ((a2 Int))(and 
(= a2 a)
(tobool  
(ll res a2)
 )
))
))

(check-sat)