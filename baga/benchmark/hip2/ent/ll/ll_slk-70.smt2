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


















































































































































































































(declare-fun n11 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next8 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q28 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs4 () __Exc)
(declare-fun flted42 () Int)
(declare-fun n () Int)
(declare-fun Anon29 () __Exc)
(declare-fun Anon28 () __Exc)
(declare-fun q29 () __Exc)
(declare-fun ys4 () __Exc)
(declare-fun m () Int)
(declare-fun m4 () Int)


(assert 
(and 
;lexvar(= n11 flted42)
(= xsprm tmpprm)
(= ysprm xs4)
(= next8 q28)
(= tmpprm q28)
(= xs4 xs)
(= ys4 ys)
(distinct xs4 nil)
(= (+ flted42 1) n)
(= Anon29 Anon28)
(= q29 ys4)
(= (+ m 1) m4)

)
)

(assert (not 
;lexvar
))

(check-sat)