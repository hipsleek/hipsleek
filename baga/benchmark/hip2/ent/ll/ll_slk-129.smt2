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


















































































































































































































(declare-fun m () Int)
(declare-fun Anon46 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next14 () node)
(declare-fun tmpprm () node)
(declare-fun q46 () node)
(declare-fun xs () node)
(declare-fun ys10 () node)
(declare-fun ys () node)
(declare-fun xs10 () node)
(declare-fun flted66 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs10)
(= next14 q46)
(= tmpprm q46)
(= xs10 xs)
(= ys10 ys)
(distinct xs10 nil)
(= (+ flted66 1) n)
(tobool (ssep 
(ll q46 flted66)
(ll ys m)
(pto xs10 (sref (ref val Anon46) (ref next ys10) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n17)
(ll ysprm m10)
) )
)
))

(check-sat)