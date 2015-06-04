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








































































































































(declare-fun Anon1 () Int)
(declare-fun Anon2_220 () node2)
(declare-fun m () Int)
(declare-fun p2 () node2)
(declare-fun q () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun tmp () node2)
(declare-fun q2 () node2)
(declare-fun q3 () node2)
(declare-fun self2 () node2)
(declare-fun p3 () node2)
(declare-fun p () node2)
(declare-fun n () Int)
(declare-fun flted1 () Int)
(declare-fun flted2_219 () Int)
(declare-fun m1 () Int)
(declare-fun n1 () Int)
(declare-fun tmpprm () node2)


(assert 
(exists ((flted2 Int)(Anon2 node2))(and 
;lexvar(= (+ flted1 1) m)
(= p2 q)
(= self2 xprm)
(distinct xprm nil)
(= yprm y)
(= xprm x)
(= tmp q2)
(= q3 self2)
(= m1 flted1)
(= p3 p)
(= n1 n)
(<= 0 n)
(<= 0 flted1)
(= flted2 (+ n1 m1))
(<= 0 m1)
(<= 0 n1)
(= tmpprm nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon1) (ref prev p2) (ref next q2) ))
(dll tmpprm Anon2 flted2)
) )
))
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)