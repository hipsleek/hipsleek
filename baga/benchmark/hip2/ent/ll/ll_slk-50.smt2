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


















































































































































































































(declare-fun n9 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next6 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q22 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs2 () __Exc)
(declare-fun flted34 () Int)
(declare-fun n () Int)
(declare-fun Anon23 () __Exc)
(declare-fun Anon22 () __Exc)
(declare-fun q23 () __Exc)
(declare-fun ys2 () __Exc)
(declare-fun m () Int)
(declare-fun m2 () Int)


(assert 
(and 
;lexvar(= n9 flted34)
(= xsprm tmpprm)
(= ysprm xs2)
(= next6 q22)
(= tmpprm q22)
(= xs2 xs)
(= ys2 ys)
(distinct xs2 nil)
(= (+ flted34 1) n)
(= Anon23 Anon22)
(= q23 ys2)
(= (+ m 1) m2)

)
)

(assert (not 
;lexvar
))

(check-sat)