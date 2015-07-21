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


















































































































































































































(declare-fun Anon70 () Int)
(declare-fun next22 () node)
(declare-fun q70 () node)
(declare-fun flted98 () Int)
(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun j () Int)
(declare-fun i () Int)


(assert 
(and 
;lexvar(= next22 q70)
(= (+ flted98 1) i)
(= xprm x)
(= yprm y)
(< 0 i)
(tobool (ssep 
(ll q70 flted98)
(ll y j)
(pto xprm (sref (ref val Anon70) (ref next yprm) ))
) )
)
)

(assert (not 
(exists ((flted99 Int))(and 
(= flted99 (+ 1 j))
(<= 0 j)
(<= 0 i)
(tobool  
(ll x flted99)
 )
))
))

(check-sat)