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
(declare-fun Anon43 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next13 () node)
(declare-fun tmpprm () node)
(declare-fun q43 () node)
(declare-fun xs () node)
(declare-fun ys9 () node)
(declare-fun ys () node)
(declare-fun xs9 () node)
(declare-fun flted62 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs9)
(= next13 q43)
(= tmpprm q43)
(= xs9 xs)
(= ys9 ys)
(distinct xs9 nil)
(= (+ flted62 1) n)
(tobool (ssep 
(ll q43 flted62)
(ll ys m)
(pto xs9 (sref (ref val Anon43) (ref next ys9) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n16)
(ll ysprm m9)
) )
)
))

(check-sat)