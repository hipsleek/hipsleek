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


















































































































































































































(declare-fun Anon43 () Int)
(declare-fun m () Int)
(declare-fun tmpprm () node)
(declare-fun q43 () node)
(declare-fun xs () node)
(declare-fun ysprm () node)
(declare-fun ys () node)
(declare-fun xsprm () node)
(declare-fun flted62 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= tmpprm q43)
(= xsprm xs)
(= ysprm ys)
(distinct xsprm nil)
(= (+ flted62 1) n)
(tobool (ssep 
(pto xsprm (sref (ref val Anon43) (ref next q43) ))
(ll q43 flted62)
(ll ys m)
) )
)
)

(assert (not 
(and 
(tobool  
(pto xsprm (sref (ref val val34prm) (ref next next34prm) ))
 )
)
))

(check-sat)