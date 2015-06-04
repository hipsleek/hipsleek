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








































































































































(declare-fun Anon8_819 () Int)
(declare-fun q6_820 () node2)
(declare-fun p () node2)
(declare-fun n () Int)
(declare-fun x () node2)
(declare-fun yprm () node2)
(declare-fun y () node2)
(declare-fun self5_817 () node2)
(declare-fun xprm () node2)
(declare-fun p6_816 () node2)
(declare-fun q () node2)
(declare-fun flted8_818 () Int)
(declare-fun m () Int)


(assert 
(exists ((p6 node2)(self5 node2)(flted8 Int)(Anon8 Int)(q6 node2))(and 
;lexvar(= xprm x)
(= yprm y)
(distinct xprm nil)
(= self5 xprm)
(= p6 q)
(= (+ flted8 1) m)
(tobool (ssep 
(pto xprm (sref (ref val Anon8) (ref prev p6) (ref next q6) ))
(dll q6 self5 flted8)
(dll y p n)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val4prm) (ref prev prev4prm) (ref next next4prm) ))
 )
)
))

(check-sat)