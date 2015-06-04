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








































































































































(declare-fun tmp2prm () node2)
(declare-fun v2_5115 () Int)
(declare-fun v3_5116 () Int)
(declare-fun tmp1_5117 () node2)
(declare-fun tmp1_5118 () node2)
(declare-fun tmp1_5119 () node2)
(declare-fun tmp1prm () node2)


(assert 
(exists ((v2 Int)(v3 Int))(and 
;lexvar(= tmp1prm nil)
(= v2 10)
(= v3 20)
(tobool (ssep 
(pto tmp2prm (sref (ref val v3) (ref prev tmp1prm) (ref next tmp1prm) ))
(pto tmp1prm (sref (ref val v2) (ref prev tmp1prm) (ref next tmp1prm) ))
(htrue )
) )
))
)

(assert (not 
(and 
(tobool  
(pto tmp1prm (sref (ref val val35prm) (ref prev prev35prm) (ref next next35prm) ))
 )
)
))

(check-sat)