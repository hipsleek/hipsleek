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








































































































































(declare-fun Anon18_1732 () Int)
(declare-fun q13_1733 () node2)
(declare-fun Anon17 () Int)
(declare-fun next4 () node2)
(declare-fun flted17 () Int)
(declare-fun p12 () node2)
(declare-fun q () node2)
(declare-fun self10 () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun y () node2)
(declare-fun m () Int)
(declare-fun q12 () node2)
(declare-fun self11_1730 () node2)
(declare-fun yprm () node2)
(declare-fun p13_1729 () node2)
(declare-fun p () node2)
(declare-fun flted18_1731 () Int)
(declare-fun n () Int)


(assert 
(exists ((p13 node2)(self11 node2)(flted18 Int)(Anon18 Int)(q13 node2))(and 
;lexvar(= next4 q12)
(= (+ flted17 1) m)
(= p12 q)
(= self10 xprm)
(= xprm x)
(= yprm y)
(< 0 m)
(= q12 nil)
(distinct yprm nil)
(= self11 yprm)
(= p13 p)
(= (+ flted18 1) n)
(tobool (ssep 
(dll q12 self10 flted17)
(pto yprm (sref (ref val Anon18) (ref prev p13) (ref next q13) ))
(dll q13 self11 flted18)
(pto xprm (sref (ref val Anon17) (ref prev p12) (ref next yprm) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto yprm (sref (ref val val9prm) (ref prev prev9prm) (ref next next9prm) ))
 )
)
))

(check-sat)