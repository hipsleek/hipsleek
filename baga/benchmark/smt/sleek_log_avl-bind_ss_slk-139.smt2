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











































































































































































(declare-fun xrightprm () node)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun tmp1prm () node)
(declare-fun aprm () NUM)
(declare-fun a () NUM)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun xvalprm () NUM)
(declare-fun Anon15 () NUM)
(declare-fun xheightprm () Int)
(declare-fun n43 () Int)
(declare-fun xleftprm () node)
(declare-fun p11 () node)
(declare-fun q11 () node)
(declare-fun tmpprm () node)
(declare-fun xright () node)
(declare-fun m34 () Int)
(declare-fun n42 () Int)
(declare-fun m51 () Int)
(declare-fun n63 () Int)
(declare-fun flted21 () Int)
(declare-fun Anon23 () Int)
(declare-fun m52 () Int)
(declare-fun m35 () Int)
(declare-fun n41 () Int)
(declare-fun m53 () Int)
(declare-fun n65 () Int)
(declare-fun n64 () Int)
(declare-fun v60prm () Int)
(declare-fun v61prm () Int)


(assert 
(and 
;lexvar(< xvalprm aprm)
(= m (+ (+ m34 1) m35))
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
(= xright q11)
(= tmpprm xright)
(= m51 m34)
(= n63 n42)
(<= 0 m34)
(<= 0 n42)
(= flted21 (+ 1 m51))
(<= 0 m51)
(<= 0 n63)
(= m52 flted21)
(= n64 Anon23)
(<= 0 flted21)
(<= 0 Anon23)
(<= 0 m52)
(<= 0 n64)
(= m53 m35)
(= n65 n41)
(<= 0 m35)
(<= 0 n41)
(<= 0 m53)
(<= 0 n65)
(= (+ v60prm n65) n64)
(= v61prm 2)
(= v60prm v61prm)
(tobool (ssep 
(avl xrightprm m52 n64)
(avl xleftprm m53 n65)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)