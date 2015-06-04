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












































(declare-fun Anon_158 () Int)
(declare-fun r_159 () node)
(declare-fun rest () node)
(declare-fun h () node)
(declare-fun hprm () node)
(declare-fun p1_156 () node)
(declare-fun restprm () node)
(declare-fun p () node)
(declare-fun flted_157 () Int)
(declare-fun n () Int)


(assert 
(exists ((p1 node)(flted Int)(Anon Int)(r node))(and 
;lexvar(= restprm rest)
(= hprm h)
(= h p)
(distinct restprm hprm)
(= p1 p)
(distinct restprm p)
(= (+ flted 1) n)
(tobool (ssep 
(pto restprm (sref (ref val Anon) (ref next r) ))
(cll r p1 flted)
) )
))
)

(assert (not 
(and 
(tobool  
(pto restprm (sref (ref val valprm) (ref next nextprm) ))
 )
)
))

(check-sat)