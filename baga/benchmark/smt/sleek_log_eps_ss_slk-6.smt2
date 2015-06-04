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











(declare-fun Anon1 () Int)
(declare-fun q1 () node)
(declare-fun flted2 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun flted3 () Int)
(declare-fun tprm () node)


(assert 
(and 
;lexvar(= tprm q1)
(= (+ flted2 1) flted3)
(= xprm x)
(= flted3 1)
(tobool (ssep 
(pto xprm (sref (ref val Anon1) (ref next q1) ))
(ll q1 flted2)
) )
)
)

(assert (not 
(= tprm nil)

))

(check-sat)