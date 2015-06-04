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
















































































































































































































































(declare-fun Anon69_5411 () Int)
(declare-fun q69_5412 () node)
(declare-fun j () Int)
(declare-fun flted97_5410 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun i () Int)


(assert 
(exists ((flted97 Int)(Anon69 Int)(q69 node))(and 
;lexvar(= (+ flted97 1) i)
(= xprm x)
(= yprm y)
(< 0 i)
(tobool (ssep 
(pto xprm (sref (ref val Anon69) (ref next q69) ))
(ll q69 flted97)
(ll y j)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val51prm) (ref next next51prm) ))
 )
)
))

(check-sat)