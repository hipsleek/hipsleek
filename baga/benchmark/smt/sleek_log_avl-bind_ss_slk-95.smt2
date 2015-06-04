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











































































































































































(declare-fun m () Int)
(declare-fun m35 () Int)
(declare-fun m34 () Int)
(declare-fun n41 () Int)
(declare-fun n42 () Int)
(declare-fun n () Int)
(declare-fun tmp1prm () node)
(declare-fun a () NUM)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun Anon15 () NUM)
(declare-fun xheightprm () Int)
(declare-fun n43 () Int)
(declare-fun xleftprm () node)
(declare-fun p11 () node)
(declare-fun xrightprm () node)
(declare-fun q11 () node)
(declare-fun xvalprm () NUM)
(declare-fun aprm () NUM)


(assert 
(and 
;lexvar(= m (+ (+ m34 1) m35))
(<= (+ 0 n42) (+ n41 1))
(<= n41 (+ 1 n42))
(= n43 n)
(distinct xprm nil)
(= tmp1prm nil)
(= aprm a)
(= xprm x)
(= xvalprm Anon15)
(= xheightprm n43)
(= xleftprm p11)
(= xrightprm q11)
(< xvalprm aprm)
(tobool (ssep 
(avl p11 m35 n41)
(avl q11 m34 n42)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)