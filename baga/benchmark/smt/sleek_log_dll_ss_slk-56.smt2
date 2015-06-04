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








































































































































(declare-fun Anon20_2117 () Int)
(declare-fun q17_2118 () node2)
(declare-fun x () node2)
(declare-fun a () Int)
(declare-fun tmp1prm () node2)
(declare-fun aprm () Int)
(declare-fun self13_2115 () node2)
(declare-fun xprm () node2)
(declare-fun p16_2114 () node2)
(declare-fun p () node2)
(declare-fun flted22_2116 () Int)
(declare-fun n () NUM)


(assert 
(exists ((p16 node2)(self13 node2)(flted22 Int)(Anon20 Int)(q17 node2))(and 
;lexvar(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(= tmp1prm nil)
(= aprm 1)
(= self13 xprm)
(= p16 p)
(= (+ flted22 1) n)
(tobool (ssep 
(pto xprm (sref (ref val Anon20) (ref prev p16) (ref next q17) ))
(dll q17 self13 flted22)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val11prm) (ref prev prev11prm) (ref next next11prm) ))
 )
)
))

(check-sat)