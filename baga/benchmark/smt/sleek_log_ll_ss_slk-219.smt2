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
















































































































































































































































(declare-fun m () Int)
(declare-fun Anon64 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next20 () node)
(declare-fun tmpprm () node)
(declare-fun q64 () node)
(declare-fun xs () node)
(declare-fun ys16 () node)
(declare-fun ys () node)
(declare-fun xs16 () node)
(declare-fun flted90 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs16)
(= next20 q64)
(= tmpprm q64)
(= xs16 xs)
(= ys16 ys)
(distinct xs16 nil)
(= (+ flted90 1) n)
(tobool (ssep 
(ll q64 flted90)
(ll ys m)
(pto xs16 (sref (ref val Anon64) (ref next ys16) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n23)
(ll ysprm m16)
) )
)
))

(check-sat)