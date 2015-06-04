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
















































































































































































































































(declare-fun n16 () Int)
(declare-fun xsprm () __Exc)
(declare-fun ysprm () __Exc)
(declare-fun next13 () __Exc)
(declare-fun tmpprm () __Exc)
(declare-fun q43 () __Exc)
(declare-fun xs () __Exc)
(declare-fun ys () __Exc)
(declare-fun xs9 () __Exc)
(declare-fun flted62 () Int)
(declare-fun n () Int)
(declare-fun Anon44 () __Exc)
(declare-fun Anon43 () __Exc)
(declare-fun q44 () __Exc)
(declare-fun ys9 () __Exc)
(declare-fun m () Int)
(declare-fun m9 () Int)


(assert 
(and 
;lexvar(= n16 flted62)
(= xsprm tmpprm)
(= ysprm xs9)
(= next13 q43)
(= tmpprm q43)
(= xs9 xs)
(= ys9 ys)
(distinct xs9 nil)
(= (+ flted62 1) n)
(= Anon44 Anon43)
(= q44 ys9)
(= (+ m 1) m9)

)
)

(assert (not 
;lexvar
))

(check-sat)