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


















































































































































































































(declare-fun n18 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next15 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q49 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs11 () __Exc)
(declare-fun flted70 () Int)
(declare-fun n () Int)
(declare-fun Anon50 () __Exc)
(declare-fun Anon49 () __Exc)
(declare-fun q50 () __Exc)
(declare-fun ys11 () __Exc)
(declare-fun m () Int)
(declare-fun m11 () Int)


(assert 
(and 
;lexvar(= n18 flted70)
(= xsprm tmpprm)
(= ysprm xs11)
(= next15 q49)
(= tmpprm q49)
(= xs11 xs)
(= ys11 ys)
(distinct xs11 nil)
(= (+ flted70 1) n)
(= Anon50 Anon49)
(= q50 ys11)
(= (+ m 1) m11)

)
)

(assert (not 
;lexvar
))

(check-sat)