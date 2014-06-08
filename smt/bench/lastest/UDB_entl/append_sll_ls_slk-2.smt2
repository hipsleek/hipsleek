(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun next () (Field node node))

(define-fun ll ((?in node))
Space (tospace
(or
(= ?in nil)
(exists ((?q_20 node))(and 
(tobool (ssep 
(pto ?in  (ref next ?q_20))
(ll ?q_20)
) )
)))))

(define-fun lseg ((?in node) (?p node))
Space (tospace
(or
(= ?in ?p)
(exists ((?p_19 node)(?q_18 node))(and 
(= ?p_19 ?p)
(tobool (ssep 
(pto ?in  (ref next ?q_18))
(lseg ?q_18 ?p_19)
) )
)))))

(define-fun ll_e1 ((?in node))
Space (tospace
(exists ((?q node))(and 
(tobool (ssep 
(pto ?in  (ref next ?q))
(ll ?q)
) )
))))

(define-fun ll_e2 ((?in node))
Space (tospace
(exists ((?p node)(?q node))(and 
(= ?p ?q)
(tobool (ssep 
(pto ?in  (ref next ?p))
(ll ?q)
) )
))))




(define-fun node_e1 ((?in node) (?q node))
Space (tospace
(exists ((?p node))(and 
(= ?p ?q)
(tobool  
(pto ?in  (ref next ?p))
 )
))))




(define-fun lseg_e1 ((?in node) (?p node))
Space (tospace
(exists ((?q node))(and 
(= ?p ?q)
(tobool  
(lseg ?in ?p)
 )
))))



(declare-fun xprm () node)
(declare-fun vprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun q () node)


(assert 
(and 
(= vprm nil)
(= vprm q)
(= xprm x)
(= yprm y)
(distinct x nil)
(tobool (ssep 
(ll q)
(pto xprm  (ref next q))
) )
)
)

(assert (not 
(and 
(= vprm nil)
(= vprm q)
(= xprm x)
(= yprm y)
(distinct x nil)
(tobool (ssep 
(ll q)
(pto xprm  (ref next q))
) )
)
))

(check-sat)