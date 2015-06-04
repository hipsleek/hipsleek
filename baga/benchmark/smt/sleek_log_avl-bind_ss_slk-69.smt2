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











































































































































































(declare-fun v26prm () Int)
(declare-fun tmp1prm () node)
(declare-fun h7 () Int)
(declare-fun dm () Int)
(declare-fun cm () Int)
(declare-fun h5 () Int)
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
(declare-fun m23 () Int)
(declare-fun n29 () Int)
(declare-fun h6 () Int)
(declare-fun n32 () Int)
(declare-fun n33 () Int)
(declare-fun n34 () Int)
(declare-fun m26 () Int)
(declare-fun m28 () Int)
(declare-fun m27 () Int)
(declare-fun Anon13 () node)
(declare-fun v1prm () node)
(declare-fun p9 () node)
(declare-fun cprm () node)
(declare-fun q9 () node)
(declare-fun dprm () node)
(declare-fun m24 () Int)
(declare-fun n30 () Int)
(declare-fun m25 () Int)
(declare-fun n31 () Int)
(declare-fun hprm () Int)
(declare-fun n35 () Int)
(declare-fun n36 () Int)
(declare-fun n37 () Int)
(declare-fun m29 () Int)
(declare-fun m31 () Int)
(declare-fun m30 () Int)


(assert 
(and 
;lexvar(<= 0 n32)
(<= 0 m26)
(= v26prm n32)
(distinct tmp1prm nil)
(<= 0 n)
(<= 0 m)
(<= 0 n29)
(<= 0 m23)
(= hprm (+ 1 h7))
;eqmax(<= 0 n31)
(<= 0 m25)
(<= 0 an4)
(<= 0 dm)
(= n31 an4)
(= m25 dm)
(<= 0 n30)
(<= 0 m24)
(<= 0 cn)
(<= 0 cm)
(= n30 cn)
(= m24 cm)
(= h6 (+ 1 h5))
;eqmax(<= 0 bn)
(<= 0 bm)
(= n29 bn)
(= m23 bm)
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
(= m28 m)
(= n33 n)
(= m27 m23)
(= n34 n29)
(<= n33 (+ 1 n34))
(<= (+ 0 n34) (+ n33 1))
(= h6 n32)
(= m26 (+ (+ m27 1) m28))
(= Anon13 v1prm)
(= p9 cprm)
(= q9 dprm)
(= m31 m24)
(= n36 n30)
(= m30 m25)
(= n37 n31)
(<= n36 (+ 1 n37))
(<= (+ 0 n37) (+ n36 1))
(= hprm n35)
(= m29 (+ (+ m30 1) m31))
(tobool  
(avl tmp1prm m26 n32)
 )
)
)

(assert (not 
;lexvar
))

(check-sat)