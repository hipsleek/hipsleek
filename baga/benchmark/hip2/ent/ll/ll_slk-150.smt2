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


















































































































































































































(declare-fun n19 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next16 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q52 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs12 () __Exc)
(declare-fun flted74 () Int)
(declare-fun n () Int)
(declare-fun Anon53 () __Exc)
(declare-fun Anon52 () __Exc)
(declare-fun q53 () __Exc)
(declare-fun ys12 () __Exc)
(declare-fun m () Int)
(declare-fun m12 () Int)


(assert 
(and 
;lexvar(= n19 flted74)
(= xsprm tmpprm)
(= ysprm xs12)
(= next16 q52)
(= tmpprm q52)
(= xs12 xs)
(= ys12 ys)
(distinct xs12 nil)
(= (+ flted74 1) n)
(= Anon53 Anon52)
(= q53 ys12)
(= (+ m 1) m12)

)
)

(assert (not 
;lexvar
))

(check-sat)