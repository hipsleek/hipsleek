(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node2 0)
(declare-fun val () (Field node2 Int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?p_40 node2)(?self_41 node2)(?flted_12_39 Int))(and 
(= (+ ?flted_12_39 1) ?n)
(= ?p_40 ?p)
(= ?self_41 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref prev ?p_40) (ref next ?q) ))
(dll ?q ?self_41 ?flted_12_39)
) )
)))))








































































































































(declare-fun t () Int)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun q () node2)
(declare-fun m () Int)


(assert 
(and 
;lexvar(= t 0)
(< 0 m)
(= xprm x)
(tobool  
(dll x q m)
 )
)
)

(assert (not 
(exists ((q33 node2)(m4 Int))(and 
(= m4 m)
(= q33 q)
(<= 0 m)
(tobool  
(dll x q33 m4)
 )
))
))

(check-sat)