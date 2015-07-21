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


















































































































































































































(declare-fun Anon52 () Int)
(declare-fun m () Int)
(declare-fun tmpprm () node)
(declare-fun q52 () node)
(declare-fun xs () node)
(declare-fun ysprm () node)
(declare-fun ys () node)
(declare-fun xsprm () node)
(declare-fun flted74 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= tmpprm q52)
(= xsprm xs)
(= ysprm ys)
(distinct xsprm nil)
(= (+ flted74 1) n)
(tobool (ssep 
(pto xsprm (sref (ref val Anon52) (ref next q52) ))
(ll q52 flted74)
(ll ys m)
) )
)
)

(assert (not 
(and 
(tobool  
(pto xsprm (sref (ref val val40prm) (ref next next40prm) ))
 )
)
))

(check-sat)