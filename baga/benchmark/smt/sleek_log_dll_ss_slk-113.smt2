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








































































































































(declare-fun Anon38_4359 () Int)
(declare-fun q38_4360 () node2)
(declare-fun flted44_4358 () Int)
(declare-fun p40_4356 () node2)
(declare-fun p () node2)
(declare-fun self31_4357 () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun n () Int)


(assert 
(exists ((p40 node2)(self31 node2)(flted44 Int)(Anon38 Int)(q38 node2))(and 
;lexvar(= (+ flted44 1) n)
(= p40 p)
(= self31 xprm)
(= xprm x)
(< 1 n)
(tobool (ssep 
(pto xprm (sref (ref val Anon38) (ref prev p40) (ref next q38) ))
(dll q38 self31 flted44)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val29prm) (ref prev prev29prm) (ref next next29prm) ))
 )
)
))

(check-sat)