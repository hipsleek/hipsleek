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























































































































































































































































































































































































































































(declare-fun Anon19 () Int)
(declare-fun q13 () node)
(declare-fun v1 () node)
(declare-fun q11 () node)
(declare-fun v50prm () node)
(declare-fun p13 () node)
(declare-fun n14 () Int)
(declare-fun m14 () Int)
(declare-fun Anon17 () Int)
(declare-fun left1 () node)
(declare-fun flted19 () Int)
(declare-fun n12 () Int)
(declare-fun m12 () Int)
(declare-fun tmpprm () node)
(declare-fun p11 () node)
(declare-fun x () node)
(declare-fun a () Int)
(declare-fun tmp1prm () node)
(declare-fun xprm () node)
(declare-fun height33 () Int)
(declare-fun n () Int)
(declare-fun height32 () Int)
(declare-fun height31 () Int)
(declare-fun m () Int)
(declare-fun size24 () Int)
(declare-fun size23 () Int)
(declare-fun aprm () Int)
(declare-fun Anon15 () Int)
(declare-fun height37 () Int)
(declare-fun n13 () Int)
(declare-fun height38 () Int)
(declare-fun height39 () Int)
(declare-fun m13 () Int)
(declare-fun size28 () Int)
(declare-fun size27 () Int)


(assert 
(and 
;lexvar(= v50prm p13)
(= (+ 2 n14) n13)
(<= 0 n14)
(<= 0 m14)
(<= 0 height32)
(<= 0 size23)
(= n14 height32)
(= m14 size23)
(<= 0 n13)
(<= 0 m13)
(<= 0 Anon17)
(<= 0 flted19)
(= n13 Anon17)
(= m13 flted19)
(= left1 p11)
(<= 0 n12)
(<= 0 m12)
(= flted19 (+ 1 m12))
(<= 0 height31)
(<= 0 size24)
(= n12 height31)
(= m12 size24)
(= tmpprm p11)
(= xprm x)
(= aprm a)
(= tmp1prm nil)
(distinct xprm nil)
(= height33 n)
(<= height31 (+ 1 height32))
(<= height32 (+ 1 height31))
(= m (+ (+ size23 1) size24))
(<= aprm Anon15)
(= height37 n13)
(<= height39 (+ 1 height38))
(<= height38 (+ 1 height39))
(= m13 (+ (+ size27 1) size28))
(tobool (ssep 
(pto v1 (sref (ref val Anon19) (ref height height37) (ref left p13) (ref right q13) ))
(avl p13 size28 height39)
(avl q13 size27 height38)
(pto xprm (sref (ref val Anon15) (ref height height33) (ref left v1) (ref right q11) ))
(avl q11 m14 n14)
) )
)
)

(assert (not 
(and 
(tobool  
(avl v50prm m15 n15)
 )
)
))

(check-sat)