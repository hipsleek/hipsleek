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








































































































































(declare-fun Anon21 () Int)
(declare-fun Anon22_2153 () Int)
(declare-fun q19_2154 () node2)
(declare-fun q18 () node2)
(declare-fun x () node2)
(declare-fun a () Int)
(declare-fun tmp1prm () node2)
(declare-fun aprm () Int)
(declare-fun xprm () node2)
(declare-fun p17 () node2)
(declare-fun p () node2)
(declare-fun n () NUM)
(declare-fun self15_2151 () node2)
(declare-fun v12prm () node2)
(declare-fun p18_2150 () node2)
(declare-fun self14 () node2)
(declare-fun flted24_2152 () Int)
(declare-fun flted23 () Int)


(assert 
(exists ((p18 node2)(self15 node2)(flted24 Int)(Anon22 Int)(q19 node2))(and 
;lexvar(= v12prm q18)
(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(= tmp1prm nil)
(= aprm 1)
(= self14 xprm)
(= p17 p)
(= (+ flted23 1) n)
(= self15 v12prm)
(= p18 self14)
(= (+ flted24 1) flted23)
(tobool (ssep 
(pto xprm (sref (ref val Anon21) (ref prev p17) (ref next q18) ))
(pto v12prm (sref (ref val Anon22) (ref prev p18) (ref next q19) ))
(dll q19 self15 flted24)
) )
))
)

(assert (not 
(and 
(tobool  
(pto v12prm (sref (ref val val12prm) (ref prev prev12prm) (ref next next12prm) ))
 )
)
))

(check-sat)