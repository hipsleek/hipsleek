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
(declare-fun Anon34 () Int)
(declare-fun xsprm () node)
(declare-fun ysprm () node)
(declare-fun next10 () node)
(declare-fun tmpprm () node)
(declare-fun q34 () node)
(declare-fun xs () node)
(declare-fun ys6 () node)
(declare-fun ys () node)
(declare-fun xs6 () node)
(declare-fun flted50 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xsprm tmpprm)
(= ysprm xs6)
(= next10 q34)
(= tmpprm q34)
(= xs6 xs)
(= ys6 ys)
(distinct xs6 nil)
(= (+ flted50 1) n)
(tobool (ssep 
(ll q34 flted50)
(ll ys m)
(pto xs6 (sref (ref val Anon34) (ref next ys6) ))
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(ll xsprm n13)
(ll ysprm m6)
) )
)
))

(check-sat)