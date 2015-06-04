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











































































































































































(declare-fun n28 () Int)
(declare-fun m21 () Int)
(declare-fun n27 () Int)
(declare-fun m22 () Int)
(declare-fun q7 () node)
(declare-fun p7 () node)
(declare-fun Anon11 () node)
(declare-fun n25 () Int)
(declare-fun m18 () Int)
(declare-fun n24 () Int)
(declare-fun m19 () Int)
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
(declare-fun m14 () Int)
(declare-fun n20 () Int)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun tmp1_3099 () node)
(declare-fun m17 () Int)
(declare-fun m16 () Int)
(declare-fun n22 () Int)
(declare-fun m15 () Int)
(declare-fun n21 () Int)
(declare-fun tmp2_3098 () node)
(declare-fun m20 () Int)
(declare-fun n23 () Int)
(declare-fun n26 () Int)
(declare-fun h_3100 () Int)
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
;lexvar(= m20 (+ (+ m21 1) m22))
(= h3 n26)
(<= (+ 0 n28) (+ n27 1))
(<= n27 (+ 1 n28))
(= n28 n22)
(= m21 m16)
(= n27 n21)
(= m22 m15)
(= q7 dprm)
(= p7 cprm)
(= Anon11 v3prm)
(= m17 (+ (+ m18 1) m19))
(= h1 n23)
(<= (+ 0 n25) (+ n24 1))
(<= n24 (+ 1 n25))
(= n25 n20)
(= m18 m14)
(= n24 n)
(= m19 m)
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
(= m14 bm)
(= n20 bn)
(<= 0 bm)
(<= 0 bn)
;eqmax(= h1 (+ 1 h))
(= m15 cm)
(= n21 cn)
(<= 0 cm)
(<= 0 cn)
(= m16 dm)
(= n22 an2)
(<= 0 dm)
(<= 0 an2)
;eqmax(= h3 (+ 1 h2))
(<= 0 m14)
(<= 0 n20)
(<= 0 m)
(<= 0 n)
(distinct tmp1prm nil)
(<= 0 m17)
(<= 0 n23)
(<= 0 m16)
(<= 0 n22)
(<= 0 m15)
(<= 0 n21)
(distinct tmp2prm nil)
(<= 0 m20)
(<= 0 n26)
;eqmax(= hprm (+ 1 h4))
(= res v19prm)
(tobool (ssep 
(avl tmp1prm m17 n23)
(avl tmp2prm m20 n26)
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