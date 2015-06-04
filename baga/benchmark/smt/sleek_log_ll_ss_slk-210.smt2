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
















































































































































































































































(declare-fun n22 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next19 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q61 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs15 () __Exc)
(declare-fun flted86 () Int)
(declare-fun n () Int)
(declare-fun Anon62 () __Exc)
(declare-fun Anon61 () __Exc)
(declare-fun q62 () __Exc)
(declare-fun ys15 () __Exc)
(declare-fun m () Int)
(declare-fun m15 () Int)


(assert 
(and 
;lexvar(= n22 flted86)
(= xsprm tmpprm)
(= ysprm xs15)
(= next19 q61)
(= tmpprm q61)
(= xs15 xs)
(= ys15 ys)
(distinct xs15 nil)
(= (+ flted86 1) n)
(= Anon62 Anon61)
(= q62 ys15)
(= (+ m 1) m15)

)
)

(assert (not 
;lexvar
))

(check-sat)