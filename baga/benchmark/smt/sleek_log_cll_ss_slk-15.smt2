(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun cll ((?in node) (?p node) (?n Int))
Space (tospace
(or
(and 
(= ?in ?p)
(= ?n 0)

)(exists ((?p_28 node)(?flted_11_27 Int))(and 
(= (+ ?flted_11_27 1) ?n)
(distinct ?in ?p)
(= ?p_28 ?p)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?r) ))
(cll ?r ?p_28 ?flted_11_27)
) )
)))))

(define-fun hd ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?self_25 node)(?flted_15_24 Int))(and 
(= (+ ?flted_15_24 1) ?n)
(= ?self_25 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref next ?r) ))
(cll ?r ?self_25 ?flted_15_24)
) )
)))))












































(declare-fun Anon1 () Int)
(declare-fun r1 () node)
(declare-fun hprm () node)
(declare-fun h () node)
(declare-fun restprm () node)
(declare-fun p3 () node)
(declare-fun p2 () node)
(declare-fun flted1 () Int)
(declare-fun n1 () Int)
(declare-fun n3 () Int)
(declare-fun rest () node)
(declare-fun p () node)
(declare-fun res () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= (+ flted1 1) n)
(distinct restprm p)
(= p2 p)
(distinct restprm hprm)
(= h p)
(= hprm h)
(= restprm rest)
(= p3 p2)
(= n1 flted1)
(<= 0 flted1)
(= n3 n1)
(<= 0 n1)
(= res (+ 1 n3))
(tobool (ssep 
(pto restprm (sref (ref val Anon1) (ref next r1) ))
(cll r1 p3 n1)
) )
)
)

(assert (not 
(exists ((p4 node)(n2 Int))(and 
(= n2 n)
(= p4 p)
(= res n)
(<= 0 n)
(tobool  
(cll rest p4 n2)
 )
))
))

(check-sat)