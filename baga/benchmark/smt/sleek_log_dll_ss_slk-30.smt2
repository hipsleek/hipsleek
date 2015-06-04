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








































































































































(declare-fun Anon9 () Int)
(declare-fun q7 () node2)
(declare-fun Anon12 () node2)
(declare-fun m () Int)
(declare-fun p7 () node2)
(declare-fun q () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun q8 () node2)
(declare-fun self6 () node2)
(declare-fun p8 () node2)
(declare-fun p () node2)
(declare-fun n () Int)
(declare-fun flted9 () Int)
(declare-fun flted12 () Int)
(declare-fun m2 () Int)
(declare-fun n2 () Int)
(declare-fun tmpprm () node2)


(assert 
(and 
;lexvar(= (+ flted9 1) m)
(= p7 q)
(= self6 xprm)
(distinct xprm nil)
(= yprm y)
(= xprm x)
(= q8 self6)
(= m2 flted9)
(= p8 p)
(= n2 n)
(<= 0 n)
(<= 0 flted9)
(= flted12 (+ n2 m2))
(<= 0 m2)
(<= 0 n2)
(distinct tmpprm nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon9) (ref prev p7) (ref next q7) ))
(dll tmpprm Anon12 flted12)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)