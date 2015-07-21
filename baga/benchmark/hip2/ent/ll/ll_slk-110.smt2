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


















































































































































































































(declare-fun n15 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next12 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q40 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs8 () __Exc)
(declare-fun flted58 () Int)
(declare-fun n () Int)
(declare-fun Anon41 () __Exc)
(declare-fun Anon40 () __Exc)
(declare-fun q41 () __Exc)
(declare-fun ys8 () __Exc)
(declare-fun m () Int)
(declare-fun m8 () Int)


(assert 
(and 
;lexvar(= n15 flted58)
(= xsprm tmpprm)
(= ysprm xs8)
(= next12 q40)
(= tmpprm q40)
(= xs8 xs)
(= ys8 ys)
(distinct xs8 nil)
(= (+ flted58 1) n)
(= Anon41 Anon40)
(= q41 ys8)
(= (+ m 1) m8)

)
)

(assert (not 
;lexvar
))

(check-sat)