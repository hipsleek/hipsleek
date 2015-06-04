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























































































































































































































































































































































































































































(declare-fun tmp2prm () node)
(declare-fun hprm () Int)
(declare-fun h2 () Int)
(declare-fun n4 () Int)
(declare-fun m4 () Int)
(declare-fun dm () Int)
(declare-fun n3 () Int)
(declare-fun m3 () Int)
(declare-fun cm () Int)
(declare-fun h () Int)
(declare-fun bm () Int)
(declare-fun am () Int)
(declare-fun a () node)
(declare-fun b () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun dprm () node)
(declare-fun d () node)
(declare-fun v1 () node)
(declare-fun v2prm () node)
(declare-fun v2 () node)
(declare-fun v3prm () Int)
(declare-fun v3 () Int)
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
(declare-fun m2 () Int)
(declare-fun n2 () Int)
(declare-fun h1 () Int)
(declare-fun n5 () Int)
(declare-fun height20 () Int)
(declare-fun height21 () Int)
(declare-fun m5 () Int)
(declare-fun size14 () Int)
(declare-fun size13 () Int)


(assert 
(and 
;lexvar(= hprm (+ 1 h2))
;eqmax(<= 0 n4)
(<= 0 m4)
(<= 0 an2)
(<= 0 dm)
(= n4 an2)
(= m4 dm)
(<= 0 n3)
(<= 0 m3)
(<= 0 cn)
(<= 0 cm)
(= n3 cn)
(= m3 cm)
(= h1 (+ 1 h))
;eqmax(<= 0 n2)
(<= 0 m2)
(<= 0 bn)
(<= 0 bm)
(= n2 bn)
(= m2 bm)
(<= 0 n)
(<= 0 m)
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
(= size14 m)
(= height20 n)
(= size13 m2)
(= height21 n2)
(<= height20 (+ 1 height21))
(<= height21 (+ 1 height20))
(= h1 n5)
(= m5 (+ (+ size13 1) size14))
(tobool (ssep 
(pto tmp2prm (sref (ref val v3prm) (ref height hprm) (ref left cprm) (ref right dprm) ))
(avl cprm m3 n3)
(avl dprm m4 n4)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)