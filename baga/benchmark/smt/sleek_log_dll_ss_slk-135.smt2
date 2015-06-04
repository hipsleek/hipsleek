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








































































































































(declare-fun tmp1_5183 () node2)
(declare-fun prev8 () node2)
(declare-fun v7 () Int)
(declare-fun v4 () Int)
(declare-fun v5 () Int)
(declare-fun tmp2_5184 () node2)
(declare-fun tmp2_5182 () node2)
(declare-fun prev7_5185 () node2)
(declare-fun prev7 () node2)
(declare-fun res () node2)


(assert 
(exists ((tmp2prm node2)(tmp1prm node2))(and 
;lexvar(= prev8 prev7)
(= v7 30)
(= prev7 nil)
(= v4 10)
(= v5 20)
(tobool (ssep 
(pto tmp2prm (sref (ref val v5) (ref prev res) (ref next tmp1prm) ))
(pto res (sref (ref val v7) (ref prev prev7) (ref next tmp2prm) ))
(pto tmp1prm (sref (ref val v4) (ref prev tmp2prm) (ref next prev7) ))
(htrue )
) )
))
)

(assert (not 
(exists ((flted52 Int)(Anon57 node2))(and 
(= flted52 3)
(tobool  
(dll res Anon57 flted52)
 )
))
))

(check-sat)