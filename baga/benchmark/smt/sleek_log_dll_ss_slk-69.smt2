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








































































































































(declare-fun Anon26_2726 () Int)
(declare-fun q23_2727 () node2)
(declare-fun x () node2)
(declare-fun a () Int)
(declare-fun tmp1prm () node2)
(declare-fun aprm () Int)
(declare-fun self19_2724 () node2)
(declare-fun xprm () node2)
(declare-fun p22_2723 () node2)
(declare-fun p () node2)
(declare-fun flted28_2725 () Int)
(declare-fun n () NUM)


(assert 
(exists ((p22 node2)(self19 node2)(flted28 Int)(Anon26 Int)(q23 node2))(and 
;lexvar(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(= tmp1prm nil)
(distinct aprm 1)
(= self19 xprm)
(= p22 p)
(= (+ flted28 1) n)
(tobool (ssep 
(pto xprm (sref (ref val Anon26) (ref prev p22) (ref next q23) ))
(dll q23 self19 flted28)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val20prm) (ref prev prev20prm) (ref next next20prm) ))
 )
)
))

(check-sat)