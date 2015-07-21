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
(declare-fun Anon31 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next9 () node)
(declare-fun tmpprm () node)
(declare-fun q31 () node)
(declare-fun xs () node)
(declare-fun ys5 () node)
(declare-fun ys () node)
(declare-fun xs5 () node)
(declare-fun flted46 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs5)
(= next9 q31)
(= tmpprm q31)
(= xs5 xs)
(= ys5 ys)
(distinct xs5 nil)
(= (+ flted46 1) n)
(tobool (ssep 
(ll q31 flted46)
(ll ys m)
(pto xs5 (sref (ref val Anon31) (ref next ys5) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n12)
(ll ysprm m5)
) )
)
))

(check-sat)