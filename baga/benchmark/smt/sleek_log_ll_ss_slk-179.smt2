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
(declare-fun Anon52 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next16 () node)
(declare-fun tmpprm () node)
(declare-fun q52 () node)
(declare-fun xs () node)
(declare-fun ys12 () node)
(declare-fun ys () node)
(declare-fun xs12 () node)
(declare-fun flted74 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs12)
(= next16 q52)
(= tmpprm q52)
(= xs12 xs)
(= ys12 ys)
(distinct xs12 nil)
(= (+ flted74 1) n)
(tobool (ssep 
(ll q52 flted74)
(ll ys m)
(pto xs12 (sref (ref val Anon52) (ref next ys12) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n19)
(ll ysprm m12)
) )
)
))

(check-sat)