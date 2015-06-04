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








































































































































(declare-fun Anon17 () Int)
(declare-fun q12 () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun xprm () node2)
(declare-fun p12 () node2)
(declare-fun q14 () node2)
(declare-fun self10 () node2)
(declare-fun p14 () node2)
(declare-fun p () node2)
(declare-fun flted17 () Int)
(declare-fun flted21_2014 () Int)
(declare-fun m3 () Int)
(declare-fun n3 () Int)
(declare-fun x () node2)
(declare-fun q () node2)
(declare-fun n () Int)
(declare-fun m () Int)


(assert 
(exists ((flted21 Int))(and 
;lexvar(distinct q12 nil)
(< 0 m)
(= yprm y)
(= xprm x)
(= self10 xprm)
(= p12 q)
(= (+ flted17 1) m)
(= q14 self10)
(= m3 flted17)
(= p14 p)
(= n3 n)
(<= 0 n)
(<= 0 flted17)
(= flted21 (+ n3 m3))
(<= 0 m3)
(<= 0 n3)
(tobool (ssep 
(pto xprm (sref (ref val Anon17) (ref prev p12) (ref next q12) ))
(dll q12 q14 flted21)
) )
))
)

(assert (not 
(exists ((q16 node2)(flted20 Int))(and 
(= q16 q)
(= flted20 (+ n m))
(<= 0 n)
(<= 0 m)
(tobool  
(dll x q16 flted20)
 )
))
))

(check-sat)