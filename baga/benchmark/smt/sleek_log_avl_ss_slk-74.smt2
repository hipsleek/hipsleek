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























































































































































































































































































































































































































































(declare-fun height27 () Int)
(declare-fun size19 () Int)
(declare-fun height26 () Int)
(declare-fun size20 () Int)
(declare-fun q9 () node)
(declare-fun p9 () node)
(declare-fun Anon13 () node)
(declare-fun height25 () Int)
(declare-fun size17 () Int)
(declare-fun height24 () Int)
(declare-fun size18 () Int)
(declare-fun q8 () node)
(declare-fun p8 () node)
(declare-fun Anon12 () node)
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
(declare-fun h6 () Int)
(declare-fun h5 () Int)
(declare-fun an4 () Int)
(declare-fun h8 () Int)
(declare-fun h7 () Int)
(declare-fun m7 () Int)
(declare-fun n7 () Int)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun tmp1_5399 () node)
(declare-fun m10 () Int)
(declare-fun m9 () Int)
(declare-fun n9 () Int)
(declare-fun m8 () Int)
(declare-fun n8 () Int)
(declare-fun tmp2_5398 () node)
(declare-fun m11 () Int)
(declare-fun n10 () Int)
(declare-fun n11 () Int)
(declare-fun h_5400 () Int)
(declare-fun h9 () Int)
(declare-fun v29prm () node)
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
;lexvar(= m11 (+ (+ size19 1) size20))
(= h8 n11)
(<= height27 (+ 1 height26))
(<= height26 (+ 1 height27))
(= height27 n9)
(= size19 m9)
(= height26 n8)
(= size20 m8)
(= q9 dprm)
(= p9 cprm)
(= Anon13 v1prm)
(= m10 (+ (+ size17 1) size18))
(= h6 n10)
(<= height25 (+ 1 height24))
(<= height24 (+ 1 height25))
(= height25 n7)
(= size17 m7)
(= height24 n)
(= size18 m)
(= q8 bprm)
(= p8 aprm)
(= Anon12 v3prm)
(= an4 an)
(<= cn (+ 1 bn))
(<= (+ 0 bn) (+ cn 1))
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
(= m7 bm)
(= n7 bn)
(<= 0 bm)
(<= 0 bn)
;eqmax(= h6 (+ 1 h5))
(= m8 cm)
(= n8 cn)
(<= 0 cm)
(<= 0 cn)
(= m9 dm)
(= n9 an4)
(<= 0 dm)
(<= 0 an4)
;eqmax(= h8 (+ 1 h7))
(<= 0 m7)
(<= 0 n7)
(<= 0 m)
(<= 0 n)
(distinct tmp1prm nil)
(<= 0 m10)
(<= 0 n10)
(<= 0 m9)
(<= 0 n9)
(<= 0 m8)
(<= 0 n8)
(distinct tmp2prm nil)
(<= 0 m11)
(<= 0 n11)
;eqmax(= hprm (+ 1 h9))
(= res v29prm)
(tobool (ssep 
(avl tmp1prm m10 n10)
(avl tmp2prm m11 n11)
(pto v29prm (sref (ref val v2prm) (ref height hprm) (ref left tmp1prm) (ref right tmp2prm) ))
) )
))
)

(assert (not 
(exists ((flted6 Int)(flted7 Int))(and 
(= flted6 (+ an 2))
(= flted7 (+ (+ (+ (+ dm bm) 3) am) cm))
(<= 0 dm)
(<= 0 cn)
(<= 0 cm)
(<= 0 bn)
(<= 0 bm)
(<= 0 an)
(<= 0 am)
(tobool  
(avl res flted7 flted6)
 )
))
))

(check-sat)