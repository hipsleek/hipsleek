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


















































































































































































































(declare-fun n12 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next9 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q31 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs5 () __Exc)
(declare-fun flted46 () Int)
(declare-fun n () Int)
(declare-fun Anon32 () __Exc)
(declare-fun Anon31 () __Exc)
(declare-fun q32 () __Exc)
(declare-fun ys5 () __Exc)
(declare-fun m () Int)
(declare-fun m5 () Int)


(assert 
(and 
;lexvar(= n12 flted46)
(= xsprm tmpprm)
(= ysprm xs5)
(= next9 q31)
(= tmpprm q31)
(= xs5 xs)
(= ys5 ys)
(distinct xs5 nil)
(= (+ flted46 1) n)
(= Anon32 Anon31)
(= q32 ys5)
(= (+ m 1) m5)

)
)

(assert (not 
;lexvar
))

(check-sat)