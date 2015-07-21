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
(declare-fun Anon61 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next19 () node)
(declare-fun tmpprm () node)
(declare-fun q61 () node)
(declare-fun xs () node)
(declare-fun ys15 () node)
(declare-fun ys () node)
(declare-fun xs15 () node)
(declare-fun flted86 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs15)
(= next19 q61)
(= tmpprm q61)
(= xs15 xs)
(= ys15 ys)
(distinct xs15 nil)
(= (+ flted86 1) n)
(tobool (ssep 
(ll q61 flted86)
(ll ys m)
(pto xs15 (sref (ref val Anon61) (ref next ys15) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n22)
(ll ysprm m15)
) )
)
))

(check-sat)