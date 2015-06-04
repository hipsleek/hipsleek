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























































































































































































































































































































































































































































(declare-fun q11 () node)
(declare-fun v1 () node)
(declare-fun Anon19 () Int)
(declare-fun p13 () node)
(declare-fun q13 () node)
(declare-fun Anon21 () Int)
(declare-fun p15 () node)
(declare-fun q15 () node)
(declare-fun height43 () Int)
(declare-fun height37 () Int)
(declare-fun Anon15 () Int)
(declare-fun height33 () Int)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun x () node)
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
(declare-fun n13 () Int)
(declare-fun size28 () Int)
(declare-fun height39 () Int)
(declare-fun size27 () Int)
(declare-fun height38 () Int)
(declare-fun m15 () Int)
(declare-fun n15 () Int)
(declare-fun m16 () Int)
(declare-fun n16 () Int)
(declare-fun m18 () Int)
(declare-fun n18 () Int)
(declare-fun m14 () Int)
(declare-fun n14 () Int)
(declare-fun size31 () Int)
(declare-fun height44 () Int)
(declare-fun size32 () Int)
(declare-fun height45 () Int)
(declare-fun m17 () Int)
(declare-fun n17 () Int)
(declare-fun flted26_19417 () Int)
(declare-fun flted25_19416 () Int)
(declare-fun am () Int)
(declare-fun an () Int)
(declare-fun bm () Int)
(declare-fun bn () Int)
(declare-fun cm () Int)
(declare-fun cn () Int)
(declare-fun dm () Int)
(declare-fun v126prm () node)
(declare-fun res () node)
(declare-fun n () Int)
(declare-fun m () Int)


(assert 
(exists ((flted25 Int)(flted26 Int))(and 
;lexvar(= m18 (+ (+ size31 1) size32))
(<= height44 (+ 1 height45))
(<= height45 (+ 1 height44))
(= height43 n18)
(<= n15 n16)
(= m13 (+ (+ size27 1) size28))
(<= height38 (+ 1 height39))
(<= height39 (+ 1 height38))
(= height37 n13)
(<= aprm Anon15)
(= m (+ (+ size23 1) size24))
(<= height32 (+ 1 height31))
(<= height31 (+ 1 height32))
(= height33 n)
(distinct xprm nil)
(= aprm a)
(= xprm x)
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
(= (+ 2 n14) n13)
(= m15 size28)
(= n15 height39)
(<= 0 size28)
(<= 0 height39)
(= m16 size27)
(= n16 height38)
(<= 0 size27)
(<= 0 height38)
(= m17 m15)
(= n17 n15)
(<= 0 m15)
(<= 0 n15)
(= m18 m16)
(= n18 n16)
(<= 0 m16)
(<= 0 n16)
(<= 0 m18)
(<= 0 n18)
(= (+ n17 1) n18)
(= am m17)
(= an n17)
(= bm size32)
(= bn height45)
(= cm size31)
(= cn height44)
(= dm m14)
(<= 0 m14)
(<= 0 n14)
(<= 0 size31)
(<= 0 height44)
(<= 0 size32)
(<= 0 height45)
(<= 0 m17)
(<= 0 n17)
(= flted26 (+ (+ (+ (+ dm bm) 3) am) cm))
(= flted25 (+ 2 an))
(<= 0 am)
(<= 0 an)
(<= 0 bm)
(<= 0 bn)
(<= 0 cm)
(<= 0 cn)
(<= 0 dm)
(= res v126prm)
(tobool (ssep 
(pto xprm (sref (ref val Anon15) (ref height height33) (ref left v1) (ref right q11) ))
(pto v1 (sref (ref val Anon19) (ref height height37) (ref left p13) (ref right q13) ))
(pto q13 (sref (ref val Anon21) (ref height height43) (ref left p15) (ref right q15) ))
(avl v126prm flted26 flted25)
) )
))
)

(assert (not 
(exists ((flted22 Int)(Anon28 Int))(and 
(= flted22 (+ 1 m))
(<= 0 n)
(<= 0 m)
(tobool  
(avl res flted22 Anon28)
 )
))
))

(check-sat)