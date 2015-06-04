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

(define-fun avl ((?in node) (?size Int) (?height Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?size 0)
(= ?height 0)

)(exists ((?height_34 Int))(and 
(= ?size (+ (+ ?size2 1) ?size1))
(<= ?height2 (+ 1 ?height1))
(<= ?height1 (+ 1 ?height2))
(= ?height_34 ?height)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref height ?height_34) (ref left ?p) (ref right ?q) ))
(avl ?p ?size1 ?height1)
(avl ?q ?size2 ?height2)
) )
)))))























































































































































































































































































































































































































































(declare-fun v9 () node)
(declare-fun q21 () node)
(declare-fun Anon30 () Int)
(declare-fun m () Int)
(declare-fun height63 () Int)
(declare-fun n () Int)
(declare-fun tmp1prm () node)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun tmpprm () node)
(declare-fun size44 () Int)
(declare-fun height61 () Int)
(declare-fun m26 () Int)
(declare-fun n26 () Int)
(declare-fun left2 () node)
(declare-fun p21 () node)
(declare-fun flted32 () Int)
(declare-fun n28 () Int)
(declare-fun m27 () Int)
(declare-fun size43 () Int)
(declare-fun height62 () Int)
(declare-fun m28 () Int)
(declare-fun n30 () Int)
(declare-fun n29 () Int)
(declare-fun v137prm () Int)
(declare-fun v138prm () Int)


(assert 
(and 
;lexvar(<= aprm Anon30)
(= m (+ (+ size43 1) size44))
(<= height62 (+ 1 height61))
(<= height61 (+ 1 height62))
(= height63 n)
(distinct xprm nil)
(= tmp1prm nil)
(= aprm a)
(= xprm x)
(= tmpprm p21)
(= m26 size44)
(= n26 height61)
(<= 0 size44)
(<= 0 height61)
(= flted32 (+ 1 m26))
(<= n26 n28)
(<= n28 (+ 1 n26))
(<= 0 m26)
(<= 0 n26)
(= left2 p21)
(= m27 flted32)
(= n29 n28)
(<= 0 flted32)
(<= 0 n28)
(<= 0 m27)
(<= 0 n29)
(= m28 size43)
(= n30 height62)
(<= 0 size43)
(<= 0 height62)
(<= 0 m28)
(<= 0 n30)
(= (+ v137prm n30) n29)
(= v138prm 2)
(distinct v137prm v138prm)
(tobool (ssep 
(avl v9 m27 n29)
(pto xprm (sref (ref val Anon30) (ref height height63) (ref left v9) (ref right q21) ))
(avl q21 m28 n30)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)