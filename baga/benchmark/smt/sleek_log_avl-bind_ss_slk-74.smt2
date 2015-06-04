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











































































































































































(declare-fun n37 () Int)
(declare-fun m30 () Int)
(declare-fun n36 () Int)
(declare-fun m31 () Int)
(declare-fun q9 () node)
(declare-fun p9 () node)
(declare-fun Anon13 () node)
(declare-fun n34 () Int)
(declare-fun m27 () Int)
(declare-fun n33 () Int)
(declare-fun m28 () Int)
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
(declare-fun m23 () Int)
(declare-fun n29 () Int)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun tmp1_5437 () node)
(declare-fun m26 () Int)
(declare-fun m25 () Int)
(declare-fun n31 () Int)
(declare-fun m24 () Int)
(declare-fun n30 () Int)
(declare-fun tmp2_5436 () node)
(declare-fun m29 () Int)
(declare-fun n32 () Int)
(declare-fun n35 () Int)
(declare-fun h_5438 () Int)
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
;lexvar(= m29 (+ (+ m30 1) m31))
(= h8 n35)
(<= (+ 0 n37) (+ n36 1))
(<= n36 (+ 1 n37))
(= n37 n31)
(= m30 m25)
(= n36 n30)
(= m31 m24)
(= q9 dprm)
(= p9 cprm)
(= Anon13 v1prm)
(= m26 (+ (+ m27 1) m28))
(= h6 n32)
(<= (+ 0 n34) (+ n33 1))
(<= n33 (+ 1 n34))
(= n34 n29)
(= m27 m23)
(= n33 n)
(= m28 m)
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
(= m23 bm)
(= n29 bn)
(<= 0 bm)
(<= 0 bn)
;eqmax(= h6 (+ 1 h5))
(= m24 cm)
(= n30 cn)
(<= 0 cm)
(<= 0 cn)
(= m25 dm)
(= n31 an4)
(<= 0 dm)
(<= 0 an4)
;eqmax(= h8 (+ 1 h7))
(<= 0 m23)
(<= 0 n29)
(<= 0 m)
(<= 0 n)
(distinct tmp1prm nil)
(<= 0 m26)
(<= 0 n32)
(<= 0 m25)
(<= 0 n31)
(<= 0 m24)
(<= 0 n30)
(distinct tmp2prm nil)
(<= 0 m29)
(<= 0 n35)
;eqmax(= hprm (+ 1 h9))
(= res v29prm)
(tobool (ssep 
(avl tmp1prm m26 n32)
(avl tmp2prm m29 n35)
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