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
(declare-fun v23_912 () node)
(declare-fun next4 () node)
(declare-fun flted26 () Int)
(declare-fun xprm () node)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun tmp_913 () node)
(declare-fun q17 () node)
(declare-fun x () node)
(declare-fun n () Int)


(assert 
(exists ((v23prm node)(tmpprm node))(and 
;lexvar(= next4 q17)
(= (+ flted26 1) n)
(= xprm x)
(= aprm a)
(< 0 n)
(= tmpprm nil)
(= q17 nil)
(tobool (ssep 
(ll q17 flted26)
(pto v23prm (sref (ref val aprm) (ref next tmpprm) ))
(pto xprm (sref (ref val Anon17) (ref next v23prm) ))
) )
))
)

(assert (not 
(exists ((flted27 Int))(and 
(= flted27 (+ 1 n))
(<= 0 n)
(tobool  
(ll x flted27)
 )
))
))

(check-sat)