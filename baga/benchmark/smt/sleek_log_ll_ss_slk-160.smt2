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
















































































































































































































































(declare-fun n17 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next14 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q46 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs10 () __Exc)
(declare-fun flted66 () Int)
(declare-fun n () Int)
(declare-fun Anon47 () __Exc)
(declare-fun Anon46 () __Exc)
(declare-fun q47 () __Exc)
(declare-fun ys10 () __Exc)
(declare-fun m () Int)
(declare-fun m10 () Int)


(assert 
(and 
;lexvar(= n17 flted66)
(= xsprm tmpprm)
(= ysprm xs10)
(= next14 q46)
(= tmpprm q46)
(= xs10 xs)
(= ys10 ys)
(distinct xs10 nil)
(= (+ flted66 1) n)
(= Anon47 Anon46)
(= q47 ys10)
(= (+ m 1) m10)

)
)

(assert (not 
;lexvar
))

(check-sat)