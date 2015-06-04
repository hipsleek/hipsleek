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








































































































































(declare-fun tmp3prm () node2)
(declare-fun v6_5144 () Int)
(declare-fun prev7 () node2)
(declare-fun v4 () Int)
(declare-fun v5 () Int)
(declare-fun tmp1_5145 () node2)
(declare-fun tmp1_5146 () node2)
(declare-fun tmp1_5147 () node2)
(declare-fun tmp1prm () node2)
(declare-fun tmp2_5148 () node2)
(declare-fun tmp2prm () node2)


(assert 
(exists ((v6 Int))(and 
;lexvar(= v6 30)
(= prev7 tmp1prm)
(= tmp1prm nil)
(= v4 10)
(= v5 20)
(tobool (ssep 
(pto tmp1prm (sref (ref val v4) (ref prev tmp2prm) (ref next tmp1prm) ))
(pto tmp2prm (sref (ref val v5) (ref prev tmp1prm) (ref next tmp1prm) ))
(pto tmp3prm (sref (ref val v6) (ref prev tmp1prm) (ref next tmp2prm) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto tmp2prm (sref (ref val val36prm) (ref prev prev36prm) (ref next next36prm) ))
 )
)
))

(check-sat)