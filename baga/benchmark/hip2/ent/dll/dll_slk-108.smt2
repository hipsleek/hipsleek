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








































































































































(declare-fun Anon37 () Int)
(declare-fun flted43 () Int)
(declare-fun p37 () node2)
(declare-fun p () node2)
(declare-fun self30 () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun aprm () node2)
(declare-fun a () node2)
(declare-fun n () Int)
(declare-fun q37 () node2)


(assert 
(and 
;lexvar(= (+ flted43 1) n)
(= p37 p)
(= self30 xprm)
(= xprm x)
(= aprm a)
(< 0 n)
(distinct q37 nil)
(not )(tobool (ssep 
(pto xprm (sref (ref val Anon37) (ref prev p37) (ref next q37) ))
(dll q37 self30 flted43)
) )
)
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val28prm) (ref prev prev28prm) (ref next next28prm) ))
 )
)
))

(check-sat)