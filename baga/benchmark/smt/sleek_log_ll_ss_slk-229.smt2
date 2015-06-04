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

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_14_23 Int))(and 
(= (+ ?flted_14_23 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q ?flted_14_23)
) )
)))))
















































































































































































































































(declare-fun m () Int)
(declare-fun Anon67 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next21 () node)
(declare-fun tmpprm () node)
(declare-fun q67 () node)
(declare-fun xs () node)
(declare-fun ys17 () node)
(declare-fun ys () node)
(declare-fun xs17 () node)
(declare-fun flted94 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs17)
(= next21 q67)
(= tmpprm q67)
(= xs17 xs)
(= ys17 ys)
(distinct xs17 nil)
(= (+ flted94 1) n)
(tobool (ssep 
(ll q67 flted94)
(ll ys m)
(pto xs17 (sref (ref val Anon67) (ref next ys17) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n24)
(ll ysprm m17)
) )
)
))

(check-sat)