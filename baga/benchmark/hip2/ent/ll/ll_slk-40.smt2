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


















































































































































































































(declare-fun n8 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next5 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q19 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs1 () __Exc)
(declare-fun flted30 () Int)
(declare-fun n () Int)
(declare-fun Anon20 () __Exc)
(declare-fun Anon19 () __Exc)
(declare-fun q20 () __Exc)
(declare-fun ys1 () __Exc)
(declare-fun m () Int)
(declare-fun m1 () Int)


(assert 
(and 
;lexvar(= n8 flted30)
(= xsprm tmpprm)
(= ysprm xs1)
(= next5 q19)
(= tmpprm q19)
(= xs1 xs)
(= ys1 ys)
(distinct xs1 nil)
(= (+ flted30 1) n)
(= Anon20 Anon19)
(= q20 ys1)
(= (+ m 1) m1)

)
)

(assert (not 
;lexvar
))

(check-sat)