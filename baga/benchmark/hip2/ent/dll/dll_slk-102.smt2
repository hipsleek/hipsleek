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








































































































































(declare-fun Anon36_3993 () Int)
(declare-fun q36_3994 () node2)
(declare-fun flted42_3992 () Int)
(declare-fun p36_3990 () node2)
(declare-fun p () node2)
(declare-fun self29_3991 () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun aprm () node2)
(declare-fun a () node2)
(declare-fun n () Int)


(assert 
(exists ((p36 node2)(self29 node2)(flted42 Int)(Anon36 Int)(q36 node2))(and 
;lexvar(= (+ flted42 1) n)
(= p36 p)
(= self29 xprm)
(= xprm x)
(= aprm a)
(< 0 n)
(tobool (ssep 
(pto xprm (sref (ref val Anon36) (ref prev p36) (ref next q36) ))
(dll q36 self29 flted42)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val26prm) (ref prev prev26prm) (ref next next26prm) ))
 )
)
))

(check-sat)