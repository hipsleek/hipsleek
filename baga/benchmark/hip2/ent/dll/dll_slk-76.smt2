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








































































































































(declare-fun Anon27 () Int)
(declare-fun q24 () node2)
(declare-fun p23 () node2)
(declare-fun a () Int)
(declare-fun xprm () node2)
(declare-fun v20_3050 () Int)
(declare-fun aprm () Int)
(declare-fun p24 () node2)
(declare-fun self20 () node2)
(declare-fun flted29 () Int)
(declare-fun flted31_3051 () Int)
(declare-fun n4 () Int)
(declare-fun x () node2)
(declare-fun p () node2)
(declare-fun n () Int)


(assert 
(exists ((v20prm Int)(flted31 Int))(and 
;lexvar(= (+ flted29 1) n)
(= p23 p)
(= self20 xprm)
(not )(distinct aprm 1)
(< 0 a)
(< a n)
(= aprm a)
(= xprm x)
(= (+ v20prm 1) aprm)
(= p24 self20)
(= n4 flted29)
(<= 0 flted29)
(= (+ flted31 1) n4)
(<= 0 n4)
(tobool (ssep 
(pto xprm (sref (ref val Anon27) (ref prev p23) (ref next q24) ))
(dll q24 p24 flted31)
) )
))
)

(assert (not 
(exists ((p25 node2)(flted30 Int))(and 
(= p25 p)
(= (+ flted30 1) n)
(<= 0 n)
(tobool  
(dll x p25 flted30)
 )
))
))

(check-sat)