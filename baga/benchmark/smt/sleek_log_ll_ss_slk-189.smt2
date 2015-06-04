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
(declare-fun Anon55 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next17 () node)
(declare-fun tmpprm () node)
(declare-fun q55 () node)
(declare-fun xs () node)
(declare-fun ys13 () node)
(declare-fun ys () node)
(declare-fun xs13 () node)
(declare-fun flted78 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs13)
(= next17 q55)
(= tmpprm q55)
(= xs13 xs)
(= ys13 ys)
(distinct xs13 nil)
(= (+ flted78 1) n)
(tobool (ssep 
(ll q55 flted78)
(ll ys m)
(pto xs13 (sref (ref val Anon55) (ref next ys13) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n20)
(ll ysprm m13)
) )
)
))

(check-sat)