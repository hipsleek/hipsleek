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








































































































































(declare-fun Anon34_3531 () Int)
(declare-fun q31_3532 () node2)
(declare-fun x () node2)
(declare-fun a () Int)
(declare-fun aprm () Int)
(declare-fun self27_3529 () node2)
(declare-fun xprm () node2)
(declare-fun p32_3528 () node2)
(declare-fun p () node2)
(declare-fun flted38_3530 () Int)
(declare-fun n () NUM)


(assert 
(exists ((p32 node2)(self27 node2)(flted38 Int)(Anon34 Int)(q31 node2))(and 
;lexvar(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(distinct aprm 1)
(not )(= self27 xprm)
(= p32 p)
(= (+ flted38 1) n)
(tobool (ssep 
(pto xprm (sref (ref val Anon34) (ref prev p32) (ref next q31) ))
(dll q31 self27 flted38)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val25prm) (ref prev prev25prm) (ref next next25prm) ))
 )
)
))

(check-sat)