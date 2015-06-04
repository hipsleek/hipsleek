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








































































































































(declare-fun Anon37 () Int)
(declare-fun v30prm () node2)
(declare-fun v_4114 () node2)
(declare-fun flted43 () Int)
(declare-fun p37 () node2)
(declare-fun p () node2)
(declare-fun self30 () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun n () Int)
(declare-fun q37 () node2)


(assert 
(exists ((v node2))(and 
;lexvar(= v nil)
(= (+ flted43 1) n)
(= p37 p)
(= self30 xprm)
(= xprm x)
(= aprm a)
(< 0 n)
(= q37 nil)
(tobool (ssep 
(pto xprm (sref (ref val Anon37) (ref prev p37) (ref next q37) ))
(dll q37 self30 flted43)
(pto v30prm (sref (ref val aprm) (ref prev xprm) (ref next v) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val27prm) (ref prev prev27prm) (ref next next27prm) ))
 )
)
))

(check-sat)