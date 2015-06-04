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
(declare-fun Anon19 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next5 () node)
(declare-fun tmpprm () node)
(declare-fun q19 () node)
(declare-fun xs () node)
(declare-fun ys1 () node)
(declare-fun ys () node)
(declare-fun xs1 () node)
(declare-fun flted30 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs1)
(= next5 q19)
(= tmpprm q19)
(= xs1 xs)
(= ys1 ys)
(distinct xs1 nil)
(= (+ flted30 1) n)
(tobool (ssep 
(ll q19 flted30)
(ll ys m)
(pto xs1 (sref (ref val Anon19) (ref next ys1) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n8)
(ll ysprm m1)
) )
)
))

(check-sat)