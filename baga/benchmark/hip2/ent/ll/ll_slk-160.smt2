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


















































































































































































































(declare-fun n20 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next17 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q55 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs13 () __Exc)
(declare-fun flted78 () Int)
(declare-fun n () Int)
(declare-fun Anon56 () __Exc)
(declare-fun Anon55 () __Exc)
(declare-fun q56 () __Exc)
(declare-fun ys13 () __Exc)
(declare-fun m () Int)
(declare-fun m13 () Int)


(assert 
(and 
;lexvar(= n20 flted78)
(= xsprm tmpprm)
(= ysprm xs13)
(= next17 q55)
(= tmpprm q55)
(= xs13 xs)
(= ys13 ys)
(distinct xs13 nil)
(= (+ flted78 1) n)
(= Anon56 Anon55)
(= q56 ys13)
(= (+ m 1) m13)

)
)

(assert (not 
;lexvar
))

(check-sat)