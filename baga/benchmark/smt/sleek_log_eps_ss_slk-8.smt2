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

)(exists ((?flted_13_27 Int))(and 
(= (+ ?flted_13_27 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q ?flted_13_27)
) )
)))))

(define-fun lseg ((?in node) (?p node) (?n Int))
Space (tospace
(or
(and 
(= ?in ?p)
(= ?n 0)

)(exists ((?p_25 node)(?flted_18_24 Int))(and 
(= (+ ?flted_18_24 1) ?n)
(= ?p_25 ?p)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref next ?q) ))
(lseg ?q ?p_25 ?flted_18_24)
) )
)))))











(declare-fun Anon2_154 () Int)
(declare-fun q2_155 () node)
(declare-fun flted4_153 () Int)
(declare-fun p1_152 () node)
(declare-fun r () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun flted5_156 () Int)


(assert 
(exists ((p1 node)(flted4 Int)(Anon2 Int)(q2 node)(flted5 Int))(and 
;lexvar(= (+ flted4 1) flted5)
(= p1 r)
(= xprm x)
(= flted5 2)
(tobool (ssep 
(pto xprm (sref (ref val Anon2) (ref next q2) ))
(lseg q2 p1 flted4)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val1prm) (ref next next1prm) ))
 )
)
))

(check-sat)