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








































































































































(declare-fun Anon11 () node2)
(declare-fun Anon9 () Int)
(declare-fun next3 () node2)
(declare-fun q7 () node2)
(declare-fun flted11 () Int)
(declare-fun n2 () Int)
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
(declare-fun tmp_1366 () node2)
(declare-fun res () node2)
(declare-fun n () Int)
(declare-fun m () Int)


(assert 
(exists ((tmpprm node2))(and 
;lexvar(= res xprm)
(= next3 q7)
(<= 0 n2)
(<= 0 m2)
(= flted11 (+ n2 m2))
(<= 0 flted9)
(<= 0 n)
(= n2 n)
(= p8 p)
(= m2 flted9)
(= q8 self6)
(= xprm x)
(= yprm y)
(distinct xprm nil)
(not )(= self6 xprm)
(= p7 q)
(= (+ flted9 1) m)
(= tmpprm nil)
(not )(tobool (ssep 
(dll tmpprm Anon11 flted11)
(pto xprm (sref (ref val Anon9) (ref prev p7) (ref next tmpprm) ))
) )
))
)

(assert (not 
(exists ((flted15 Int)(Anon15 node2))(and 
(= flted15 (+ n m))
(<= 0 n)
(<= 0 m)
(tobool  
(dll res Anon15 flted15)
 )
))
))

(check-sat)