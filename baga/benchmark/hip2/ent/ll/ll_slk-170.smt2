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


















































































































































































































(declare-fun n21 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next18 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q58 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs14 () __Exc)
(declare-fun flted82 () Int)
(declare-fun n () Int)
(declare-fun Anon59 () __Exc)
(declare-fun Anon58 () __Exc)
(declare-fun q59 () __Exc)
(declare-fun ys14 () __Exc)
(declare-fun m () Int)
(declare-fun m14 () Int)


(assert 
(and 
;lexvar(= n21 flted82)
(= xsprm tmpprm)
(= ysprm xs14)
(= next18 q58)
(= tmpprm q58)
(= xs14 xs)
(= ys14 ys)
(distinct xs14 nil)
(= (+ flted82 1) n)
(= Anon59 Anon58)
(= q59 ys14)
(= (+ m 1) m14)

)
)

(assert (not 
;lexvar
))

(check-sat)