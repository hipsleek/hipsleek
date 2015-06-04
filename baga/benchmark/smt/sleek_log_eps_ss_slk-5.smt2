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











(declare-fun Anon_98 () Int)
(declare-fun q_99 () node)
(declare-fun flted_97 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun flted1_100 () Int)


(assert 
(exists ((flted Int)(Anon Int)(q node)(flted1 Int))(and 
;lexvar(= (+ flted 1) flted1)
(= xprm x)
(= flted1 1)
(tobool (ssep 
(pto xprm (sref (ref val Anon) (ref next q) ))
(ll q flted)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val valprm) (ref next nextprm) ))
 )
)
))

(check-sat)