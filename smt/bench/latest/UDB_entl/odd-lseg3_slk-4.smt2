(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


(declare-sort node 0)
(declare-fun nxt () (Field node node))

(define-fun olseg ((?in node) (?p node))
Space (tospace
(or
(and 
(tobool  
(pto ?in  (ref nxt ?p))
 )
)(exists ((?a node)(?b node))(and 
(tobool (ssep 
(pto ?in  (ref nxt ?a))
(pto ?a  (ref nxt ?b))
(olseg ?b ?p)
) )
)))))










(declare-fun b () node)
(declare-fun x () node)
(declare-fun p () node)


(assert 
(and 
(tobool (ssep 
(pto x  (ref nxt b))
(olseg b p)
) )
)
)

(assert (not 
(and 
(tobool  
(olseg x p)
 )
)
))

(check-sat)