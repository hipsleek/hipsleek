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


















































































































































































































(declare-fun n10 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next7 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q25 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs3 () __Exc)
(declare-fun flted38 () Int)
(declare-fun n () Int)
(declare-fun Anon26 () __Exc)
(declare-fun Anon25 () __Exc)
(declare-fun q26 () __Exc)
(declare-fun ys3 () __Exc)
(declare-fun m () Int)
(declare-fun m3 () Int)


(assert 
(and 
;lexvar(= n10 flted38)
(= xsprm tmpprm)
(= ysprm xs3)
(= next7 q25)
(= tmpprm q25)
(= xs3 xs)
(= ys3 ys)
(distinct xs3 nil)
(= (+ flted38 1) n)
(= Anon26 Anon25)
(= q26 ys3)
(= (+ m 1) m3)

)
)

(assert (not 
;lexvar
))

(check-sat)