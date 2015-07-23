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








































































































































(declare-fun Anon50 () Int)
(declare-fun Anon51 () node2)
(declare-fun next13 () node2)
(declare-fun Anon52 () node2)
(declare-fun xprm () node2)
(declare-fun tmp2 () node2)
(declare-fun tmp2prm () node2)
(declare-fun x () node2)


(assert 
(and 
;lexvar(= next13 Anon52)
(= xprm x)
(= tmp2prm tmp2)
(= tmp2 nil)
(= tmp2prm nil)
(not )(tobool  
(pto xprm (sref (ref val Anon50) (ref prev Anon51) (ref next tmp2prm) ))
 )
)
)

(assert (not 
(exists ((Anon55 node2)(Anon56 Int))(and 
(tobool  
(dll x Anon55 Anon56)
 )
))
))

(check-sat)