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


















































































































































































































(declare-fun Anon66_4714 () Int)
(declare-fun q66_4715 () node)
(declare-fun m () Int)
(declare-fun xs () node)
(declare-fun ysprm () node)
(declare-fun ys () node)
(declare-fun xsprm () node)
(declare-fun flted93_4713 () Int)
(declare-fun n () Int)


(assert 
(exists ((flted93 Int)(Anon66 Int)(q66 node))(and 
;lexvar(= xsprm xs)
(= ysprm ys)
(distinct xsprm nil)
(= (+ flted93 1) n)
(tobool (ssep 
(pto xsprm (sref (ref val Anon66) (ref next q66) ))
(ll q66 flted93)
(ll ys m)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xsprm (sref (ref val val49prm) (ref next next49prm) ))
 )
)
))

(check-sat)