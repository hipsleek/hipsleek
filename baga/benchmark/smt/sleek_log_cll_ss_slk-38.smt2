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












































(declare-fun Anon9 () Int)
(declare-fun tmpprm () node)
(declare-fun flted10 () Int)
(declare-fun self6 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun v11prm () Int)
(declare-fun v () Int)
(declare-fun n () Int)
(declare-fun r9_905 () node)
(declare-fun r9 () node)


(assert 
(and 
;lexvar(= (+ flted10 1) n)
(= self6 xprm)
(= xprm x)
(= v11prm v)
(< 0 n)
(tobool (ssep 
(pto xprm (sref (ref val Anon9) (ref next r9) ))
(cll r9 self6 flted10)
(pto tmpprm (sref (ref val v11prm) (ref next r9) ))
) )
)
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val7prm) (ref next next7prm) ))
 )
)
))

(check-sat)