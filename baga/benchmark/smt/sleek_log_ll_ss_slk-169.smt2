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
(declare-fun Anon49 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next15 () node)
(declare-fun tmpprm () node)
(declare-fun q49 () node)
(declare-fun xs () node)
(declare-fun ys11 () node)
(declare-fun ys () node)
(declare-fun xs11 () node)
(declare-fun flted70 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs11)
(= next15 q49)
(= tmpprm q49)
(= xs11 xs)
(= ys11 ys)
(distinct xs11 nil)
(= (+ flted70 1) n)
(tobool (ssep 
(ll q49 flted70)
(ll ys m)
(pto xs11 (sref (ref val Anon49) (ref next ys11) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n18)
(ll ysprm m11)
) )
)
))

(check-sat)