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























































































































































































































































































































































































































































(declare-fun p11 () node)
(declare-fun v5 () node)
(declare-fun Anon25 () Int)
(declare-fun q17 () node)
(declare-fun p17 () node)
(declare-fun Anon27 () Int)
(declare-fun p19 () node)
(declare-fun q19 () node)
(declare-fun height55 () Int)
(declare-fun height49 () Int)
(declare-fun Anon15 () Int)
(declare-fun height33 () Int)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun size23 () Int)
(declare-fun height32 () Int)
(declare-fun m19 () Int)
(declare-fun n19 () Int)
(declare-fun right1 () node)
(declare-fun q11 () node)
(declare-fun flted21 () Int)
(declare-fun Anon23 () Int)
(declare-fun m20 () Int)
(declare-fun size24 () Int)
(declare-fun height31 () Int)
(declare-fun n20 () Int)
(declare-fun size35 () Int)
(declare-fun height50 () Int)
(declare-fun size36 () Int)
(declare-fun height51 () Int)
(declare-fun m23 () Int)
(declare-fun n23 () Int)
(declare-fun m24 () Int)
(declare-fun n24 () Int)
(declare-fun m22 () Int)
(declare-fun n22 () Int)
(declare-fun m25 () Int)
(declare-fun n25 () Int)
(declare-fun size39 () Int)
(declare-fun height56 () Int)
(declare-fun size40 () Int)
(declare-fun height57 () Int)
(declare-fun m21 () Int)
(declare-fun n21 () Int)
(declare-fun flted30_19783 () Int)
(declare-fun flted29_19782 () Int)
(declare-fun am () Int)
(declare-fun an () Int)
(declare-fun bm () Int)
(declare-fun bn () Int)
(declare-fun cm () Int)
(declare-fun cn () Int)
(declare-fun dm () Int)
(declare-fun v128prm () node)
(declare-fun res () node)
(declare-fun n () Int)
(declare-fun m () Int)


(assert 
(exists ((flted29 Int)(flted30 Int))(and 
;lexvar(= m24 (+ (+ size39 1) size40))
(<= height56 (+ 1 height57))
(<= height57 (+ 1 height56))
(= height55 n24)
(<= n22 n23)
(= m20 (+ (+ size35 1) size36))
(<= height50 (+ 1 height51))
(<= height51 (+ 1 height50))
(= height49 n20)
(< Anon15 aprm)
(= m (+ (+ size23 1) size24))
(<= height32 (+ 1 height31))
(<= height31 (+ 1 height32))
(= height33 n)
(distinct xprm nil)
(= aprm a)
(= xprm x)
(= m19 size23)
(= n19 height32)
(<= 0 size23)
(<= 0 height32)
(= flted21 (+ 1 m19))
(<= 0 m19)
(<= 0 n19)
(= right1 q11)
(= m20 flted21)
(= n20 Anon23)
(<= 0 flted21)
(<= 0 Anon23)
(<= 0 m20)
(<= 0 n20)
(= m21 size24)
(= n21 height31)
(<= 0 size24)
(<= 0 height31)
(= (+ 2 n21) n20)
(= m22 size35)
(= n22 height50)
(<= 0 size35)
(<= 0 height50)
(= m23 size36)
(= n23 height51)
(<= 0 size36)
(<= 0 height51)
(= m24 m23)
(= n24 n23)
(<= 0 m23)
(<= 0 n23)
(<= 0 m24)
(<= 0 n24)
(= (+ n25 1) n24)
(= m25 m22)
(= n25 n22)
(<= 0 m22)
(<= 0 n22)
(= am m21)
(= an n21)
(= bm size40)
(= bn height57)
(= cm size39)
(= cn height56)
(= dm m25)
(<= 0 m25)
(<= 0 n25)
(<= 0 size39)
(<= 0 height56)
(<= 0 size40)
(<= 0 height57)
(<= 0 m21)
(<= 0 n21)
(= flted30 (+ (+ (+ (+ dm bm) 3) am) cm))
(= flted29 (+ an 2))
(<= 0 am)
(<= 0 an)
(<= 0 bm)
(<= 0 bn)
(<= 0 cm)
(<= 0 cn)
(<= 0 dm)
(= res v128prm)
(tobool (ssep 
(pto xprm (sref (ref val Anon15) (ref height height33) (ref left p11) (ref right v5) ))
(pto v5 (sref (ref val Anon25) (ref height height49) (ref left p17) (ref right q17) ))
(pto p17 (sref (ref val Anon27) (ref height height55) (ref left p19) (ref right q19) ))
(avl v128prm flted30 flted29)
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