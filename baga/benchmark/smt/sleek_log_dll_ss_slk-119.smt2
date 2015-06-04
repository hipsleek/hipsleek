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








































































































































(declare-fun Anon39 () Int)
(declare-fun Anon41 () Int)
(declare-fun Anon42_4566 () Int)
(declare-fun q42_4567 () node2)
(declare-fun q41 () node2)
(declare-fun q39 () node2)
(declare-fun p41 () node2)
(declare-fun p () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun n () Int)
(declare-fun tmp1prm () node2)
(declare-fun p43 () node2)
(declare-fun self32 () node2)
(declare-fun flted45 () Int)
(declare-fun self35_4564 () node2)
(declare-fun tmp2prm () node2)
(declare-fun p44_4563 () node2)
(declare-fun self34 () node2)
(declare-fun flted48_4565 () Int)
(declare-fun flted47 () Int)


(assert 
(exists ((p44 node2)(self35 node2)(flted48 Int)(Anon42 Int)(q42 node2))(and 
;lexvar(= tmp2prm q41)
(= tmp1prm q39)
(= (+ flted45 1) n)
(= p41 p)
(= self32 xprm)
(= xprm x)
(< 1 n)
(= self34 tmp1prm)
(= p43 self32)
(= (+ flted47 1) flted45)
(distinct tmp2prm nil)
(= self35 tmp2prm)
(= p44 self34)
(= (+ flted48 1) flted47)
(tobool (ssep 
(pto xprm (sref (ref val Anon39) (ref prev p41) (ref next q39) ))
(pto tmp1prm (sref (ref val Anon41) (ref prev p43) (ref next q41) ))
(pto tmp2prm (sref (ref val Anon42) (ref prev p44) (ref next q42) ))
(dll q42 self35 flted48)
) )
))
)

(assert (not 
(and 
(tobool  
(pto tmp2prm (sref (ref val val31prm) (ref prev prev31prm) (ref next next31prm) ))
 )
)
))

(check-sat)