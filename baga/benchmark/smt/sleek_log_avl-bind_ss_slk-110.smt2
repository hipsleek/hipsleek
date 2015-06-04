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











































































































































































(declare-fun n54 () Int)
(declare-fun m44 () Int)
(declare-fun v45prm () Int)
(declare-fun n53 () Int)
(declare-fun m43 () Int)
(declare-fun xleftrightprm () node)
(declare-fun q13 () node)
(declare-fun xleftleftprm () node)
(declare-fun p13 () node)
(declare-fun xleftheightprm () Int)
(declare-fun xleftvalprm () node)
(declare-fun Anon19 () node)
(declare-fun n46 () Int)
(declare-fun m38 () Int)
(declare-fun Anon17 () Int)
(declare-fun flted19 () Int)
(declare-fun n44 () Int)
(declare-fun m36 () Int)
(declare-fun tmpprm () node)
(declare-fun xrightprm () node)
(declare-fun q11 () node)
(declare-fun xleft () node)
(declare-fun p11 () node)
(declare-fun xheightprm () Int)
(declare-fun Anon15 () NUM)
(declare-fun x () node)
(declare-fun a () NUM)
(declare-fun tmp1prm () node)
(declare-fun xprm () node)
(declare-fun n43 () Int)
(declare-fun n () Int)
(declare-fun n42 () Int)
(declare-fun n41 () Int)
(declare-fun m () Int)
(declare-fun m35 () Int)
(declare-fun m34 () Int)
(declare-fun aprm () NUM)
(declare-fun xvalprm () NUM)
(declare-fun n50 () Int)
(declare-fun n45 () Int)
(declare-fun n51 () Int)
(declare-fun n52 () Int)
(declare-fun m37 () Int)
(declare-fun m42 () Int)
(declare-fun m41 () Int)


(assert 
(and 
;lexvar(= n54 n51)
(= m44 m41)
(<= 0 n53)
(<= 0 m43)
(= v45prm n53)
(<= 0 n52)
(<= 0 m42)
(= n53 n52)
(= m43 m42)
(= xleftrightprm q13)
(= xleftleftprm p13)
(= xleftheightprm n50)
(= xleftvalprm Anon19)
(= (+ 2 n46) n45)
(<= 0 n46)
(<= 0 m38)
(<= 0 n42)
(<= 0 m34)
(= n46 n42)
(= m38 m34)
(<= 0 n45)
(<= 0 m37)
(<= 0 Anon17)
(<= 0 flted19)
(= n45 Anon17)
(= m37 flted19)
(<= 0 n44)
(<= 0 m36)
(= flted19 (+ 1 m36))
(<= 0 n41)
(<= 0 m35)
(= n44 n41)
(= m36 m35)
(= tmpprm xleft)
(= xrightprm q11)
(= xleft p11)
(= xheightprm n43)
(= xvalprm Anon15)
(= xprm x)
(= aprm a)
(= tmp1prm nil)
(distinct xprm nil)
(= n43 n)
(<= n41 (+ 1 n42))
(<= (+ 0 n42) (+ n41 1))
(= m (+ (+ m34 1) m35))
(<= aprm xvalprm)
(= n50 n45)
(<= n52 (+ 1 n51))
(<= (+ 0 n51) (+ n52 1))
(= m37 (+ (+ m41 1) m42))
(tobool (ssep 
(avl xrightprm m38 n46)
(avl xleftleftprm m43 n53)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)