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
(declare-fun Anon40 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next12 () node)
(declare-fun tmpprm () node)
(declare-fun q40 () node)
(declare-fun xs () node)
(declare-fun ys8 () node)
(declare-fun ys () node)
(declare-fun xs8 () node)
(declare-fun flted58 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs8)
(= next12 q40)
(= tmpprm q40)
(= xs8 xs)
(= ys8 ys)
(distinct xs8 nil)
(= (+ flted58 1) n)
(tobool (ssep 
(ll q40 flted58)
(ll ys m)
(pto xs8 (sref (ref val Anon40) (ref next ys8) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n15)
(ll ysprm m8)
) )
)
))

(check-sat)