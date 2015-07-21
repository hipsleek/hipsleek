(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/hip/
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

)(exists ((?p_41 node2)(?self_42 node2)(?flted_12_40 Int))(and 
(= (+ ?flted_12_40 1) ?n)
(= ?p_41 ?p)
(= ?self_42 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref prev ?p_41) (ref next ?q) ))
(dll ?q ?self_42 ?flted_12_40)
) )
)))))








































































































































(declare-fun Anon17 () Int)
(declare-fun p () node2)
(declare-fun n () Int)
(declare-fun v9prm () node2)
(declare-fun flted17 () Int)
(declare-fun p12 () node2)
(declare-fun q () node2)
(declare-fun self10 () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun m () Int)
(declare-fun q12 () node2)


(assert 
(and 
;lexvar(= v9prm q12)
(= (+ flted17 1) m)
(= p12 q)
(= self10 xprm)
(= xprm x)
(= yprm y)
(< 0 m)
(distinct q12 nil)
(not )(tobool (ssep 
(pto xprm (sref (ref val Anon17) (ref prev p12) (ref next q12) ))
(dll q12 self10 flted17)
(dll y p n)
) )
)
)

(assert (not 
(and 
(< 0 m3)
(tobool (ssep 
(dll v9prm q14 m3)
(dll yprm p14 n3)
) )
)
))

(check-sat)