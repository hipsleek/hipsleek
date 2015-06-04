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
















































































































































































































































(declare-fun Anon5 () Int)
(declare-fun Anon6_777 () Int)
(declare-fun q6_778 () node)
(declare-fun v14prm () node)
(declare-fun q5 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun a () Int)
(declare-fun aprm () Int)
(declare-fun n () NUM)
(declare-fun flted10_776 () Int)
(declare-fun flted9 () Int)


(assert 
(exists ((flted10 Int)(Anon6 Int)(q6 node))(and 
;lexvar(= v14prm q5)
(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(= aprm 1)
(= (+ flted9 1) n)
(= (+ flted10 1) flted9)
(tobool (ssep 
(pto xprm (sref (ref val Anon5) (ref next q5) ))
(pto v14prm (sref (ref val Anon6) (ref next q6) ))
(ll q6 flted10)
) )
))
)

(assert (not 
(and 
(tobool  
(pto v14prm (sref (ref val val7prm) (ref next next7prm) ))
 )
)
))

(check-sat)