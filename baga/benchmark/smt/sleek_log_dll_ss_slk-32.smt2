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
(declare-fun Anon14 () Int)
(declare-fun q10 () node2)
(declare-fun prev1 () node2)
(declare-fun n2 () Int)
(declare-fun n () Int)
(declare-fun p8 () node2)
(declare-fun p () node2)
(declare-fun m2 () Int)
(declare-fun q8 () node2)
(declare-fun x () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun self6 () node2)
(declare-fun xprm () node2)
(declare-fun p7 () node2)
(declare-fun q () node2)
(declare-fun flted9 () Int)
(declare-fun m () Int)
(declare-fun self8 () node2)
(declare-fun tmpprm () node2)
(declare-fun p10 () node2)
(declare-fun Anon12 () node2)
(declare-fun flted14 () Int)
(declare-fun flted12 () Int)


(assert 
(and 
;lexvar(= prev1 p10)
(<= 0 n2)
(<= 0 m2)
(= flted12 (+ n2 m2))
(<= 0 flted9)
(<= 0 n)
(= n2 n)
(= p8 p)
(= m2 flted9)
(= q8 self6)
(= xprm x)
(= yprm y)
(distinct xprm nil)
(= self6 xprm)
(= p7 q)
(= (+ flted9 1) m)
(distinct tmpprm nil)
(= self8 tmpprm)
(= p10 Anon12)
(= (+ flted14 1) flted12)
(tobool (ssep 
(pto xprm (sref (ref val Anon9) (ref prev p7) (ref next q7) ))
(dll q10 self8 flted14)
(pto tmpprm (sref (ref val Anon14) (ref prev xprm) (ref next q10) ))
) )
)
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val6prm) (ref prev prev6prm) (ref next next6prm) ))
 )
)
))

(check-sat)