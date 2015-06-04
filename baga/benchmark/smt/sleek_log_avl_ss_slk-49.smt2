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























































































































































































































































































































































































































































(declare-fun height23 () Int)
(declare-fun size15 () Int)
(declare-fun height22 () Int)
(declare-fun size16 () Int)
(declare-fun q7 () node)
(declare-fun p7 () node)
(declare-fun Anon11 () node)
(declare-fun height21 () Int)
(declare-fun size13 () Int)
(declare-fun height20 () Int)
(declare-fun size14 () Int)
(declare-fun q6 () node)
(declare-fun p6 () node)
(declare-fun Anon10 () node)
(declare-fun v3prm () node)
(declare-fun v3 () node)
(declare-fun v2prm () Int)
(declare-fun v2 () Int)
(declare-fun v1prm () node)
(declare-fun v1 () node)
(declare-fun dprm () node)
(declare-fun d () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun h1 () Int)
(declare-fun h () Int)
(declare-fun an2 () Int)
(declare-fun h3 () Int)
(declare-fun h2 () Int)
(declare-fun m2 () Int)
(declare-fun n2 () Int)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun tmp1_3075 () node)
(declare-fun m5 () Int)
(declare-fun m4 () Int)
(declare-fun n4 () Int)
(declare-fun m3 () Int)
(declare-fun n3 () Int)
(declare-fun tmp2_3074 () node)
(declare-fun m6 () Int)
(declare-fun n5 () Int)
(declare-fun n6 () Int)
(declare-fun h_3076 () Int)
(declare-fun h4 () Int)
(declare-fun v19prm () node)
(declare-fun res () node)
(declare-fun dm () Int)
(declare-fun cn () Int)
(declare-fun cm () Int)
(declare-fun bn () Int)
(declare-fun bm () Int)
(declare-fun an () Int)
(declare-fun am () Int)


(assert 
(exists ((tmp2prm node)(tmp1prm node)(hprm Int))(and 
;lexvar(= m6 (+ (+ size15 1) size16))
(= h3 n6)
(<= height23 (+ 1 height22))
(<= height22 (+ 1 height23))
(= height23 n4)
(= size15 m4)
(= height22 n3)
(= size16 m3)
(= q7 dprm)
(= p7 cprm)
(= Anon11 v3prm)
(= m5 (+ (+ size13 1) size14))
(= h1 n5)
(<= height21 (+ 1 height20))
(<= height20 (+ 1 height21))
(= height21 n2)
(= size13 m2)
(= height20 n)
(= size14 m)
(= q6 bprm)
(= p6 aprm)
(= Anon10 v1prm)
(= an2 an)
(<= bn (+ 1 cn))
(<= (+ 0 cn) (+ bn 1))
;eqmax(= v3prm v3)
(= v2prm v2)
(= v1prm v1)
(= dprm d)
(= cprm c)
(= bprm b)
(= aprm a)
(= m am)
(= n an)
(<= 0 am)
(<= 0 an)
(= m2 bm)
(= n2 bn)
(<= 0 bm)
(<= 0 bn)
;eqmax(= h1 (+ 1 h))
(= m3 cm)
(= n3 cn)
(<= 0 cm)
(<= 0 cn)
(= m4 dm)
(= n4 an2)
(<= 0 dm)
(<= 0 an2)
;eqmax(= h3 (+ 1 h2))
(<= 0 m2)
(<= 0 n2)
(<= 0 m)
(<= 0 n)
(distinct tmp1prm nil)
(<= 0 m5)
(<= 0 n5)
(<= 0 m4)
(<= 0 n4)
(<= 0 m3)
(<= 0 n3)
(distinct tmp2prm nil)
(<= 0 m6)
(<= 0 n6)
;eqmax(= hprm (+ 1 h4))
(= res v19prm)
(tobool (ssep 
(avl tmp1prm m5 n5)
(avl tmp2prm m6 n6)
(pto v19prm (sref (ref val v2prm) (ref height hprm) (ref left tmp1prm) (ref right tmp2prm) ))
) )
))
)

(assert (not 
(exists ((flted4 Int)(flted5 Int))(and 
(= flted4 (+ 2 an))
(= flted5 (+ (+ (+ (+ dm bm) 3) am) cm))
(<= 0 dm)
(<= 0 cn)
(<= 0 cm)
(<= 0 bn)
(<= 0 bm)
(<= 0 an)
(<= 0 am)
(tobool  
(avl res flted5 flted4)
 )
))
))

(check-sat)