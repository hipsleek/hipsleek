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
(declare-fun v26prm () Int)
(declare-fun tmp1prm () node)
(declare-fun hprm () Int)
(declare-fun h7 () Int)
(declare-fun n9 () Int)
(declare-fun m9 () Int)
(declare-fun dm () Int)
(declare-fun n8 () Int)
(declare-fun m8 () Int)
(declare-fun cm () Int)
(declare-fun h5 () Int)
(declare-fun bm () Int)
(declare-fun am () Int)
(declare-fun a () node)
(declare-fun b () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun dprm () node)
(declare-fun d () node)
(declare-fun v1prm () Int)
(declare-fun v1 () Int)
(declare-fun v2prm () node)
(declare-fun v2 () node)
(declare-fun v3 () node)
(declare-fun cn () Int)
(declare-fun bn () Int)
(declare-fun an4 () Int)
(declare-fun an () Int)
(declare-fun Anon12 () node)
(declare-fun v3prm () node)
(declare-fun p8 () node)
(declare-fun aprm () node)
(declare-fun q8 () node)
(declare-fun bprm () node)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun m7 () Int)
(declare-fun n7 () Int)
(declare-fun h6 () Int)
(declare-fun n10 () Int)
(declare-fun height24 () Int)
(declare-fun height25 () Int)
(declare-fun m10 () Int)
(declare-fun size18 () Int)
(declare-fun size17 () Int)


(assert 
(and 
;lexvar(<= 0 n10)
(<= 0 m10)
(= v26prm n10)
(distinct tmp1prm nil)
(<= 0 n)
(<= 0 m)
(<= 0 n7)
(<= 0 m7)
(= hprm (+ 1 h7))
;eqmax(<= 0 n9)
(<= 0 m9)
(<= 0 an4)
(<= 0 dm)
(= n9 an4)
(= m9 dm)
(<= 0 n8)
(<= 0 m8)
(<= 0 cn)
(<= 0 cm)
(= n8 cn)
(= m8 cm)
(= h6 (+ 1 h5))
;eqmax(<= 0 bn)
(<= 0 bm)
(= n7 bn)
(= m7 bm)
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
;eqmax(<= (+ 0 bn) (+ cn 1))
(<= cn (+ 1 bn))
(= an4 an)
(= Anon12 v3prm)
(= p8 aprm)
(= q8 bprm)
(= size18 m)
(= height24 n)
(= size17 m7)
(= height25 n7)
(<= height24 (+ 1 height25))
(<= height25 (+ 1 height24))
(= h6 n10)
(= m10 (+ (+ size17 1) size18))
(tobool (ssep 
(pto tmp2prm (sref (ref val v1prm) (ref height hprm) (ref left cprm) (ref right dprm) ))
(avl cprm m8 n8)
(avl dprm m9 n9)
(avl tmp1prm m10 n10)
) )
)
)

(assert (not 
(and 
(tobool  
(avl tmp2prm m11 n11)
 )
)
))

(check-sat)