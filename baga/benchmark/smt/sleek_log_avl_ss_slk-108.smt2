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























































































































































































































































































































































































































































(declare-fun v1 () node)
(declare-fun q11 () node)
(declare-fun Anon15 () Int)
(declare-fun m () Int)
(declare-fun height33 () Int)
(declare-fun n () Int)
(declare-fun tmp1prm () node)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun tmpprm () node)
(declare-fun size24 () Int)
(declare-fun height31 () Int)
(declare-fun m12 () Int)
(declare-fun n12 () Int)
(declare-fun left1 () node)
(declare-fun p11 () node)
(declare-fun flted19 () Int)
(declare-fun Anon17 () Int)
(declare-fun m13 () Int)
(declare-fun size23 () Int)
(declare-fun height32 () Int)
(declare-fun m14 () Int)
(declare-fun n14 () Int)
(declare-fun n13 () Int)
(declare-fun v46prm () Int)
(declare-fun v47prm () Int)


(assert 
(and 
;lexvar(<= aprm Anon15)
(= m (+ (+ size23 1) size24))
(<= height32 (+ 1 height31))
(<= height31 (+ 1 height32))
(= height33 n)
(distinct xprm nil)
(= tmp1prm nil)
(= aprm a)
(= xprm x)
(= tmpprm p11)
(= m12 size24)
(= n12 height31)
(<= 0 size24)
(<= 0 height31)
(= flted19 (+ 1 m12))
(<= 0 m12)
(<= 0 n12)
(= left1 p11)
(= m13 flted19)
(= n13 Anon17)
(<= 0 flted19)
(<= 0 Anon17)
(<= 0 m13)
(<= 0 n13)
(= m14 size23)
(= n14 height32)
(<= 0 size23)
(<= 0 height32)
(<= 0 m14)
(<= 0 n14)
(= (+ v46prm n14) n13)
(= v47prm 2)
(= v46prm v47prm)
(tobool (ssep 
(avl v1 m13 n13)
(pto xprm (sref (ref val Anon15) (ref height height33) (ref left v1) (ref right q11) ))
(avl q11 m14 n14)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)