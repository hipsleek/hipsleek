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








































































































































(declare-fun Anon41 () Int)
(declare-fun Anon39 () Int)
(declare-fun next11 () node2)
(declare-fun self34 () node2)
(declare-fun q39 () node2)
(declare-fun p41 () node2)
(declare-fun p () node2)
(declare-fun xprm () node2)
(declare-fun p43 () node2)
(declare-fun self32 () node2)
(declare-fun flted47 () Int)
(declare-fun flted45 () Int)
(declare-fun q41_4789 () node2)
(declare-fun q41 () node2)
(declare-fun x () node2)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= next11 q39)
(= self34 q39)
(= (+ flted45 1) n)
(= p41 p)
(= self32 xprm)
(= xprm x)
(< 1 n)
(= p43 self32)
(= (+ flted47 1) flted45)
(= q41 nil)
(tobool (ssep 
(pto self34 (sref (ref val Anon41) (ref prev p43) (ref next q41) ))
(dll q41 self34 flted47)
(pto xprm (sref (ref val Anon39) (ref prev p41) (ref next q41) ))
) )
)
)

(assert (not 
(exists ((Anon44 node2)(Anon45 Int))(and 
(<= 0 n)
(tobool  
(dll x Anon44 Anon45)
 )
))
))

(check-sat)