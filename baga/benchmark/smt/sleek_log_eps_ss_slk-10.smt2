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

)(exists ((?flted_13_27 Int))(and 
(= (+ ?flted_13_27 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q ?flted_13_27)
) )
)))))

(define-fun lseg ((?in node) (?p node) (?n Int))
Space (tospace
(or
(and 
(= ?in ?p)
(= ?n 0)

)(exists ((?p_25 node)(?flted_18_24 Int))(and 
(= (+ ?flted_18_24 1) ?n)
(= ?p_25 ?p)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref next ?q) ))
(lseg ?q ?p_25 ?flted_18_24)
) )
)))))











(declare-fun Anon3 () Int)
(declare-fun q3 () node)
(declare-fun Anon5 () Int)
(declare-fun q5 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun flted6 () Int)
(declare-fun p4 () node)
(declare-fun p2 () node)
(declare-fun flted9 () Int)
(declare-fun flted7 () Int)
(declare-fun res () node)
(declare-fun r () node)


(assert 
(and 
;lexvar(= res q5)
(= (+ flted7 1) flted6)
(= p2 r)
(= xprm x)
(= flted6 2)
(= p4 p2)
(= (+ flted9 1) flted7)
(tobool (ssep 
(pto xprm (sref (ref val Anon3) (ref next q3) ))
(pto q3 (sref (ref val Anon5) (ref next q5) ))
(lseg q5 p4 flted9)
) )
)
)

(assert (not 
(and 
(= res r)

)
))

(check-sat)