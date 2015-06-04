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











































































































































































(declare-fun xleftprm () node)
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
(declare-fun p11 () node)
(declare-fun xrightprm () node)
(declare-fun q11 () node)
(declare-fun tmpprm () node)
(declare-fun xleft () node)
(declare-fun m35 () Int)
(declare-fun n41 () Int)
(declare-fun m36 () Int)
(declare-fun n44 () Int)
(declare-fun flted19 () Int)
(declare-fun Anon17 () Int)
(declare-fun m37 () Int)
(declare-fun m34 () Int)
(declare-fun n42 () Int)
(declare-fun m38 () Int)
(declare-fun n46 () Int)
(declare-fun n45 () Int)
(declare-fun v42prm () Int)
(declare-fun v43prm () Int)


(assert 
(and 
;lexvar(<= aprm xvalprm)
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
(= xleft p11)
(= xrightprm q11)
(= tmpprm xleft)
(= m36 m35)
(= n44 n41)
(<= 0 m35)
(<= 0 n41)
(= flted19 (+ 1 m36))
(<= 0 m36)
(<= 0 n44)
(= m37 flted19)
(= n45 Anon17)
(<= 0 flted19)
(<= 0 Anon17)
(<= 0 m37)
(<= 0 n45)
(= m38 m34)
(= n46 n42)
(<= 0 m34)
(<= 0 n42)
(<= 0 m38)
(<= 0 n46)
(= (+ v42prm n46) n45)
(= v43prm 2)
(distinct v42prm v43prm)
(tobool (ssep 
(avl xleftprm m37 n45)
(avl xrightprm m38 n46)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)