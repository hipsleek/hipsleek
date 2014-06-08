(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node2 0)
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2))
Space (tospace
(or
(= ?in nil)
(exists ((?p_20 node2)(?self_21 node2)(?q_19 node2))(and 
(= ?p_20 ?p)
(= ?self_21 ?in)
(tobool (ssep 
(pto ?in (sref (ref prev ?p_20) (ref next ?q_19) ))
(dll ?q_19 ?self_21)
) )
)))))

(define-fun dll_e1 ((?in node2) (?q node2))
Space (tospace
(exists ((?p1 node2)(?s node2)(?q1 node2))(and 
(= ?in ?s)
(= ?p1 ?q)
(tobool (ssep 
(dll ?q1 ?s)
(pto ?in (sref (ref prev ?p1) (ref next ?q1) ))
) )
))))

(define-fun dll_e2 ((?in node2) (?q node2))
Space (tospace
(exists ((?s node2)(?p1 node2)(?p2 node2)(?n node2)(?q1 node2))(and 
(= ?n ?q1)
(= ?p1 ?p2)
(= ?s ?in)
(= ?p2 ?q)
(tobool (ssep 
(pto ?in (sref (ref prev ?p1) (ref next ?n) ))
(dll ?q1 ?s)
) )
))))




(define-fun node2_e1 ((?in node2) (?p node2) (?q node2))
Space (tospace
(exists ((?p1 node2)(?n1 node2))(and 
(= ?p1 ?p)
(= ?n1 ?q)
(tobool  
(pto ?in (sref (ref prev ?p1) (ref next ?n1) ))
 )
))))






(define-fun dll_e3 ((?in node2) (?p node2))
Space (tospace
(exists ((?q node2))(and 
(= ?q ?p)
(tobool  
(dll ?in ?q)
 )
))))





(declare-fun p () node2)
(declare-fun p1 () node2)
(declare-fun q () node2)
(declare-fun q1 () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun self () node2)
(declare-fun xprm () node2)
(declare-fun p2 () node2)
(declare-fun q2 () node2)


(assert 
(and 
(= p p1)
(= q self)
(distinct q1 nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(= self xprm)
(= p2 q2)
(tobool (ssep 
(pto xprm (sref (ref prev p2) (ref next q1) ))
(dll q1 q)
) )
)
)

(assert (not 
(and 
(= p p1)
(= q self)
(distinct q1 nil)
(= xprm x)
(= yprm y)
(distinct x nil)
(= self xprm)
(= p2 q2)
(tobool  
(dll_e3 x q2)
 )
)
))

(check-sat)