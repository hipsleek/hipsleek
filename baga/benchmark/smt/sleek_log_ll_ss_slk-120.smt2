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
















































































































































































































































(declare-fun n13 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next10 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q34 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs6 () __Exc)
(declare-fun flted50 () Int)
(declare-fun n () Int)
(declare-fun Anon35 () __Exc)
(declare-fun Anon34 () __Exc)
(declare-fun q35 () __Exc)
(declare-fun ys6 () __Exc)
(declare-fun m () Int)
(declare-fun m6 () Int)


(assert 
(and 
;lexvar(= n13 flted50)
(= xsprm tmpprm)
(= ysprm xs6)
(= next10 q34)
(= tmpprm q34)
(= xs6 xs)
(= ys6 ys)
(distinct xs6 nil)
(= (+ flted50 1) n)
(= Anon35 Anon34)
(= q35 ys6)
(= (+ m 1) m6)

)
)

(assert (not 
;lexvar
))

(check-sat)