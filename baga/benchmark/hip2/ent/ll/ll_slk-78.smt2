(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/hip/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_14_24 Int))(and 
(= (+ ?flted_14_24 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref next ?q) ))
(ll ?q ?flted_14_24)
) )
)))))


















































































































































































































(declare-fun Anon31 () Int)
(declare-fun m () Int)
(declare-fun tmpprm () node)
(declare-fun q31 () node)
(declare-fun xs () node)
(declare-fun ysprm () node)
(declare-fun ys () node)
(declare-fun xsprm () node)
(declare-fun flted46 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= tmpprm q31)
(= xsprm xs)
(= ysprm ys)
(distinct xsprm nil)
(= (+ flted46 1) n)
(tobool (ssep 
(pto xsprm (sref (ref val Anon31) (ref next q31) ))
(ll q31 flted46)
(ll ys m)
) )
)
)

(assert (not 
(and 
(tobool  
(pto xsprm (sref (ref val val26prm) (ref next next26prm) ))
 )
)
))

(check-sat)