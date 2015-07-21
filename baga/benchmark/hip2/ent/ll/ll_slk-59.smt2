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
(declare-fun Anon25 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next7 () node)
(declare-fun tmpprm () node)
(declare-fun q25 () node)
(declare-fun xs () node)
(declare-fun ys3 () node)
(declare-fun ys () node)
(declare-fun xs3 () node)
(declare-fun flted38 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs3)
(= next7 q25)
(= tmpprm q25)
(= xs3 xs)
(= ys3 ys)
(distinct xs3 nil)
(= (+ flted38 1) n)
(tobool (ssep 
(ll q25 flted38)
(ll ys m)
(pto xs3 (sref (ref val Anon25) (ref next ys3) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n10)
(ll ysprm m3)
) )
)
))

(check-sat)