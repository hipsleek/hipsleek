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


















































































































































































































(declare-fun n14 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next11 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q37 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs7 () __Exc)
(declare-fun flted54 () Int)
(declare-fun n () Int)
(declare-fun Anon38 () __Exc)
(declare-fun Anon37 () __Exc)
(declare-fun q38 () __Exc)
(declare-fun ys7 () __Exc)
(declare-fun m () Int)
(declare-fun m7 () Int)


(assert 
(and 
;lexvar(= n14 flted54)
(= xsprm tmpprm)
(= ysprm xs7)
(= next11 q37)
(= tmpprm q37)
(= xs7 xs)
(= ys7 ys)
(distinct xs7 nil)
(= (+ flted54 1) n)
(= Anon38 Anon37)
(= q38 ys7)
(= (+ m 1) m7)

)
)

(assert (not 
;lexvar
))

(check-sat)