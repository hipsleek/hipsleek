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
(declare-fun tmp_929 () node)
(declare-fun next1 () node)
(declare-fun r9 () node)
(declare-fun flted10 () Int)
(declare-fun self6 () node)
(declare-fun xprm () node)
(declare-fun v11prm () Int)
(declare-fun v () Int)
(declare-fun x () node)
(declare-fun n () Int)


(assert 
(exists ((tmpprm node))(and 
;lexvar(= next1 r9)
(= (+ flted10 1) n)
(= self6 xprm)
(= xprm x)
(= v11prm v)
(< 0 n)
(tobool (ssep 
(cll r9 self6 flted10)
(pto tmpprm (sref (ref val v11prm) (ref next r9) ))
(pto xprm (sref (ref val Anon9) (ref next tmpprm) ))
) )
))
)

(assert (not 
(exists ((flted11 Int))(and 
(= flted11 (+ 1 n))
(<= 0 n)
(tobool  
(hd x flted11)
 )
))
))

(check-sat)