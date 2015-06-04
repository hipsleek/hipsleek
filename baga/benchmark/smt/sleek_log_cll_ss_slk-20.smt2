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












































(declare-fun Anon2_427 () Int)
(declare-fun r2_428 () node)
(declare-fun x () node)
(declare-fun self1_425 () node)
(declare-fun xprm () node)
(declare-fun flted2_426 () Int)
(declare-fun n () Int)


(assert 
(exists ((self1 node)(flted2 Int)(Anon2 Int)(r2 node))(and 
;lexvar(= xprm x)
(distinct xprm nil)
(= self1 xprm)
(= (+ flted2 1) n)
(tobool (ssep 
(pto xprm (sref (ref val Anon2) (ref next r2) ))
(cll r2 self1 flted2)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val1prm) (ref next next1prm) ))
 )
)
))

(check-sat)