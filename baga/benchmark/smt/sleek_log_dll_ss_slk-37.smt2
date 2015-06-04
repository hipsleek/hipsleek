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








































































































































(declare-fun Anon16_1440 () Int)
(declare-fun q11_1441 () node2)
(declare-fun p () node2)
(declare-fun n () Int)
(declare-fun flted16_1439 () Int)
(declare-fun p11_1437 () node2)
(declare-fun q () node2)
(declare-fun self9_1438 () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun m () Int)


(assert 
(exists ((p11 node2)(self9 node2)(flted16 Int)(Anon16 Int)(q11 node2))(and 
;lexvar(= (+ flted16 1) m)
(= p11 q)
(= self9 xprm)
(= xprm x)
(= yprm y)
(< 0 m)
(tobool (ssep 
(pto xprm (sref (ref val Anon16) (ref prev p11) (ref next q11) ))
(dll q11 self9 flted16)
(dll y p n)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val7prm) (ref prev prev7prm) (ref next next7prm) ))
 )
)
))

(check-sat)