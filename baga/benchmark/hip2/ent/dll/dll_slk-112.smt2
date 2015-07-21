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
(declare-fun q37 () node2)
(declare-fun aprm () node2)
(declare-fun a () node2)
(declare-fun xprm () node2)
(declare-fun p37 () node2)
(declare-fun p38 () node2)
(declare-fun self30 () node2)
(declare-fun flted43 () Int)
(declare-fun m8_4301 () Int)
(declare-fun n6 () Int)
(declare-fun x () node2)
(declare-fun p () node2)
(declare-fun n () Int)


(assert 
(exists ((m8 Int)(lprm boolean))(and 
;lexvar(not )(distinct q37 nil)
(< 0 n)
(= aprm a)
(= xprm x)
(= self30 xprm)
(= p37 p)
(= (+ flted43 1) n)
(= p38 self30)
(= n6 flted43)
(<= 0 flted43)
(< n6 m8)
(<= 0 n6)
(tobool (ssep 
(pto xprm (sref (ref val Anon37) (ref prev p37) (ref next q37) ))
(dll q37 p38 m8)
) )
))
)

(assert (not 
(exists ((p39 node2)(m7 Int))(and 
(= p39 p)
(< n m7)
(<= 0 n)
(tobool  
(dll x p39 m7)
 )
))
))

(check-sat)