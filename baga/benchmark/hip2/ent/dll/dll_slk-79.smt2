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








































































































































(declare-fun Anon28_3144 () Int)
(declare-fun q25_3145 () node2)
(declare-fun x () node2)
(declare-fun a () Int)
(declare-fun aprm () Int)
(declare-fun self21_3142 () node2)
(declare-fun xprm () node2)
(declare-fun p26_3141 () node2)
(declare-fun p () node2)
(declare-fun flted32_3143 () Int)
(declare-fun n () NUM)


(assert 
(exists ((p26 node2)(self21 node2)(flted32 Int)(Anon28 Int)(q25 node2))(and 
;lexvar(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(= aprm 1)
(= self21 xprm)
(= p26 p)
(= (+ flted32 1) n)
(tobool (ssep 
(pto xprm (sref (ref val Anon28) (ref prev p26) (ref next q25) ))
(dll q25 self21 flted32)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val21prm) (ref prev prev21prm) (ref next next21prm) ))
 )
)
))

(check-sat)