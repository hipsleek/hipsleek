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


















































































































































































































(declare-fun tmp_428 () node)
(declare-fun aprm () Int)
(declare-fun a1 () Int)
(declare-fun v11_427 () Int)
(declare-fun v10prm () node)
(declare-fun res () node)
(declare-fun a () Int)


(assert 
(exists ((v11prm Int)(tmpprm node))(and 
;lexvar(not )(distinct a1 0)
(<= 0 a)
(= a1 a)
(= (+ aprm 1) a1)
(= v11prm 0)
(= res v10prm)
(tobool (ssep 
(ll tmpprm aprm)
(pto v10prm (sref (ref val v11prm) (ref next tmpprm) ))
) )
))
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