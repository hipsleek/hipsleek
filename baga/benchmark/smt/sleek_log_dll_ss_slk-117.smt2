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
(declare-fun flted47 () Int)
(declare-fun p43 () node2)
(declare-fun self34 () node2)
(declare-fun x () node2)
(declare-fun self32 () node2)
(declare-fun xprm () node2)
(declare-fun p41 () node2)
(declare-fun p () node2)
(declare-fun flted45 () Int)
(declare-fun n () Int)
(declare-fun tmp1prm () node2)
(declare-fun q39 () node2)
(declare-fun q41 () node2)
(declare-fun tmp2prm () node2)


(assert 
(and 
;lexvar(= (+ flted47 1) flted45)
(= p43 self32)
(= self34 tmp1prm)
(< 1 n)
(= xprm x)
(= self32 xprm)
(= p41 p)
(= (+ flted45 1) n)
(= tmp1prm q39)
(= tmp2prm q41)
(distinct tmp2prm nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon39) (ref prev p41) (ref next q39) ))
(pto tmp1prm (sref (ref val Anon41) (ref prev p43) (ref next q41) ))
(dll q41 self34 flted47)
) )
)
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)