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








































































































































(declare-fun Anon29 () Int)
(declare-fun Anon30_3177 () Int)
(declare-fun q27_3178 () node2)
(declare-fun q26 () node2)
(declare-fun x () node2)
(declare-fun a () Int)
(declare-fun aprm () Int)
(declare-fun xprm () node2)
(declare-fun p27 () node2)
(declare-fun p () node2)
(declare-fun n () NUM)
(declare-fun self23_3175 () node2)
(declare-fun v23prm () node2)
(declare-fun p28_3174 () node2)
(declare-fun self22 () node2)
(declare-fun flted34_3176 () Int)
(declare-fun flted33 () Int)


(assert 
(exists ((p28 node2)(self23 node2)(flted34 Int)(Anon30 Int)(q27 node2))(and 
;lexvar(= v23prm q26)
(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(= aprm 1)
(= self22 xprm)
(= p27 p)
(= (+ flted33 1) n)
(= self23 v23prm)
(= p28 self22)
(= (+ flted34 1) flted33)
(tobool (ssep 
(pto xprm (sref (ref val Anon29) (ref prev p27) (ref next q26) ))
(pto v23prm (sref (ref val Anon30) (ref prev p28) (ref next q27) ))
(dll q27 self23 flted34)
) )
))
)

(assert (not 
(and 
(tobool  
(pto v23prm (sref (ref val val22prm) (ref prev prev22prm) (ref next next22prm) ))
 )
)
))

(check-sat)