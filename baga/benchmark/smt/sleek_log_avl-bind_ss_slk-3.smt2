(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun height () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun avl ((?in node) (?m Int) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?m 0)
(= ?n 0)

)(exists ((?n_33 Int))(and 
(= ?m (+ (+ ?m2 1) ?m1))
(<= (+ 0 ?n2) (+ ?n1 1))
(<= ?n1 (+ 1 ?n2))
(= ?n_33 ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref height ?n_33) (ref left ?p) (ref right ?q) ))
(avl ?p ?m1 ?n1)
(avl ?q ?m2 ?n2)
) )
)))))











































































































































































(declare-fun Anon_90 () Int)
(declare-fun p_91 () node)
(declare-fun q_94 () node)
(declare-fun my () Int)
(declare-fun mx () Int)
(declare-fun m1_92 () Int)
(declare-fun m2_95 () Int)
(declare-fun n2_93 () Int)
(declare-fun n3_96 () Int)
(declare-fun n1_89 () Int)
(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun nx1_97 () Int)
(declare-fun nx () Int)
(declare-fun vprm () Int)


(assert 
(exists ((n1 Int)(Anon Int)(p node)(m1 Int)(n2 Int)(q node)(m2 Int)(n3 Int)(nx1 Int))(and 
;lexvar(= mx (+ (+ m2 1) m1))
(<= (+ 0 n3) (+ n2 1))
(<= n2 (+ 1 n3))
(= n1 nx)
(= xprm x)
(= yprm y)
(distinct x nil)
(= nx1 nx)
(= vprm 0)
(tobool (ssep 
(pto xprm (sref (ref val Anon) (ref height n1) (ref left p) (ref right q) ))
(avl p m1 n2)
(avl q m2 n3)
(avl y my nx1)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val valprm) (ref height heightprm) (ref left leftprm) (ref right rightprm) ))
 )
)
))

(check-sat)