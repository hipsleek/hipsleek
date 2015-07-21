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


















































































































































































































(declare-fun v44prm () NUM)
(declare-fun v45prm () NUM)
(declare-fun i () Int)
(declare-fun xprm () node)
(declare-fun x () node)


(assert 
(and 
;lexvar(< v44prm v45prm)
(= v44prm 3)
(= v45prm 4)
(< 0 i)
(= xprm x)
(tobool  
(ll x i)
 )
)
)

(assert (not 
;lexvar
))

(check-sat)