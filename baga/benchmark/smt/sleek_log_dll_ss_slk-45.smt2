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








































































































































(declare-fun p () node2)
(declare-fun n () Int)
(declare-fun Anon17 () Int)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun self10 () node2)
(declare-fun xprm () node2)
(declare-fun p12 () node2)
(declare-fun q () node2)
(declare-fun flted17 () Int)
(declare-fun m () Int)
(declare-fun next4 () node2)
(declare-fun q12 () node2)
(declare-fun yprm () node2)


(assert 
(and 
;lexvar(= q12 nil)
(< 0 m)
(= yprm y)
(= xprm x)
(= self10 xprm)
(= p12 q)
(= (+ flted17 1) m)
(= next4 q12)
(distinct yprm nil)
(tobool (ssep 
(dll q12 self10 flted17)
(dll y p n)
(pto xprm (sref (ref val Anon17) (ref prev p12) (ref next yprm) ))
) )
)
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)