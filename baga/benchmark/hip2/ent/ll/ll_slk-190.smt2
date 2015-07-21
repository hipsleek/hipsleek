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


















































































































































































































(declare-fun n23 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next20 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q64 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs16 () __Exc)
(declare-fun flted90 () Int)
(declare-fun n () Int)
(declare-fun Anon65 () __Exc)
(declare-fun Anon64 () __Exc)
(declare-fun q65 () __Exc)
(declare-fun ys16 () __Exc)
(declare-fun m () Int)
(declare-fun m16 () Int)


(assert 
(and 
;lexvar(= n23 flted90)
(= xsprm tmpprm)
(= ysprm xs16)
(= next20 q64)
(= tmpprm q64)
(= xs16 xs)
(= ys16 ys)
(distinct xs16 nil)
(= (+ flted90 1) n)
(= Anon65 Anon64)
(= q65 ys16)
(= (+ m 1) m16)

)
)

(assert (not 
;lexvar
))

(check-sat)