(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun lseg ((?in node) (?p node) (?n Int))
Space (tospace
(or
(and 
(= ?in ?p)
(= ?n 0)

)(exists ((?p_29 node)(?flted_11_28 Int))(and 
(= (+ ?flted_11_28 1) ?n)
(= ?p_29 ?p)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref next ?q) ))
(lseg ?q ?p_29 ?flted_11_28)
) )
)))))

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_7_31 Int))(and 
(= (+ ?flted_7_31 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q ?flted_7_31)
) )
)))))

(define-fun clist ((?in node) (?n Int))
Space (tospace
(exists ((?self_26 node)(?flted_14_25 Int))(and 
(= (+ ?flted_14_25 1) ?n)
(= ?self_26 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref next ?p) ))
(lseg ?p ?self_26 ?flted_14_25)
) )
))))



































































(declare-fun Anon5 () Int)
(declare-fun q5 () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun flted6 () Int)
(declare-fun n11 () Int)
(declare-fun x () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flprm boolean))(and 
;lexvar(distinct q5 nil)
(< 0 n)
(= yprm y)
(= xprm x)
(= (+ flted6 1) n)
(= n11 flted6)
(<= 0 flted6)
(<= 0 n11)
(tobool (ssep 
(pto xprm (sref (ref val Anon5) (ref next q5) ))
(ll y m)
(lseg q5 yprm n11)
) )
))
)

(assert (not 
(exists ((e Int))(and 
(= e (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll x e)
 )
))
))

(check-sat)