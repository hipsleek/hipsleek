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











































































































































































(declare-fun v18prm () Int)
(declare-fun hprm () Int)
(declare-fun tmp2prm () node)
(declare-fun tmp1prm () node)
(declare-fun h2 () Int)
(declare-fun dm () Int)
(declare-fun cm () Int)
(declare-fun h () Int)
(declare-fun bm () Int)
(declare-fun am () Int)
(declare-fun a () node)
(declare-fun b () node)
(declare-fun c () node)
(declare-fun d () node)
(declare-fun v1 () node)
(declare-fun v2prm () node)
(declare-fun v2 () node)
(declare-fun v3 () node)
(declare-fun bn () Int)
(declare-fun cn () Int)
(declare-fun an2 () Int)
(declare-fun an () Int)
(declare-fun Anon10 () node)
(declare-fun v1prm () node)
(declare-fun p6 () node)
(declare-fun aprm () node)
(declare-fun q6 () node)
(declare-fun bprm () node)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun m14 () Int)
(declare-fun n20 () Int)
(declare-fun h1 () Int)
(declare-fun n23 () Int)
(declare-fun n24 () Int)
(declare-fun n25 () Int)
(declare-fun m17 () Int)
(declare-fun m19 () Int)
(declare-fun m18 () Int)
(declare-fun Anon11 () node)
(declare-fun v3prm () node)
(declare-fun p7 () node)
(declare-fun cprm () node)
(declare-fun q7 () node)
(declare-fun dprm () node)
(declare-fun m15 () Int)
(declare-fun n21 () Int)
(declare-fun m16 () Int)
(declare-fun n22 () Int)
(declare-fun h3 () Int)
(declare-fun n26 () Int)
(declare-fun n27 () Int)
(declare-fun n28 () Int)
(declare-fun m20 () Int)
(declare-fun m22 () Int)
(declare-fun m21 () Int)


(assert 
(and 
;lexvar(= v18prm 1)
;eqmax(<= 0 n26)
(<= 0 m20)
(distinct tmp2prm nil)
(<= 0 n21)
(<= 0 m15)
(<= 0 n22)
(<= 0 m16)
(<= 0 n23)
(<= 0 m17)
(distinct tmp1prm nil)
(<= 0 n)
(<= 0 m)
(<= 0 n20)
(<= 0 m14)
(= h3 (+ 1 h2))
;eqmax(<= 0 an2)
(<= 0 dm)
(= n22 an2)
(= m16 dm)
(<= 0 cn)
(<= 0 cm)
(= n21 cn)
(= m15 cm)
(= h1 (+ 1 h))
;eqmax(<= 0 bn)
(<= 0 bm)
(= n20 bn)
(= m14 bm)
(<= 0 an)
(<= 0 am)
(= n an)
(= m am)
(= aprm a)
(= bprm b)
(= cprm c)
(= dprm d)
(= v1prm v1)
(= v2prm v2)
(= v3prm v3)
;eqmax(<= (+ 0 cn) (+ bn 1))
(<= bn (+ 1 cn))
(= an2 an)
(= Anon10 v1prm)
(= p6 aprm)
(= q6 bprm)
(= m19 m)
(= n24 n)
(= m18 m14)
(= n25 n20)
(<= n24 (+ 1 n25))
(<= (+ 0 n25) (+ n24 1))
(= h1 n23)
(= m17 (+ (+ m18 1) m19))
(= Anon11 v3prm)
(= p7 cprm)
(= q7 dprm)
(= m22 m15)
(= n27 n21)
(= m21 m16)
(= n28 n22)
(<= n27 (+ 1 n28))
(<= (+ 0 n28) (+ n27 1))
(= h3 n26)
(= m20 (+ (+ m21 1) m22))
(tobool (ssep 
(avl tmp1prm m17 n23)
(avl tmp2prm m20 n26)
) )
)
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)