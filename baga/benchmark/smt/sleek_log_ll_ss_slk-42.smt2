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
















































































































































































































































(declare-fun Anon9 () Int)
(declare-fun n5 () Int)
(declare-fun v18prm () Int)
(declare-fun v17prm () node)
(declare-fun q9 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun a () Int)
(declare-fun aprm () Int)
(declare-fun flted13 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= n5 flted13)
(= (+ v18prm 1) aprm)
(= v17prm q9)
(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(distinct aprm 1)
(= (+ flted13 1) n)
(tobool  
(pto xprm (sref (ref val Anon9) (ref next q9) ))
 )
)
)

(assert (not 
;lexvar
))

(check-sat)