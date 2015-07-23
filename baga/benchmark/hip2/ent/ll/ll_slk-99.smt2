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


















































































































































































































(declare-fun m () Int)
(declare-fun Anon37 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next11 () node)
(declare-fun tmpprm () node)
(declare-fun q37 () node)
(declare-fun xs () node)
(declare-fun ys7 () node)
(declare-fun ys () node)
(declare-fun xs7 () node)
(declare-fun flted54 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs7)
(= next11 q37)
(= tmpprm q37)
(= xs7 xs)
(= ys7 ys)
(distinct xs7 nil)
(= (+ flted54 1) n)
(tobool (ssep 
(ll q37 flted54)
(ll ys m)
(pto xs7 (sref (ref val Anon37) (ref next ys7) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n14)
(ll ysprm m7)
) )
)
))

(check-sat)