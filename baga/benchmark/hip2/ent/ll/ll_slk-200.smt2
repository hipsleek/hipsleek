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


















































































































































































































(declare-fun n24 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next21 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q67 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs17 () __Exc)
(declare-fun flted94 () Int)
(declare-fun n () Int)
(declare-fun Anon68 () __Exc)
(declare-fun Anon67 () __Exc)
(declare-fun q68 () __Exc)
(declare-fun ys17 () __Exc)
(declare-fun m () Int)
(declare-fun m17 () Int)


(assert 
(and 
;lexvar(= n24 flted94)
(= xsprm tmpprm)
(= ysprm xs17)
(= next21 q67)
(= tmpprm q67)
(= xs17 xs)
(= ys17 ys)
(distinct xs17 nil)
(= (+ flted94 1) n)
(= Anon68 Anon67)
(= q68 ys17)
(= (+ m 1) m17)

)
)

(assert (not 
;lexvar
))

(check-sat)