(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun ele () (Field node Int))
(declare-fun height () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun avl ((?in node) (?m Int) (?n Int) (?bal Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?m 0)
(= ?n 0)
(= ?bal 1)

)(exists ((?n_80 Int))(and 
(= ?m (+ (+ ?m2 1) ?m1))
(<= (+ 0 ?n2) (+ ?n1 1))
(<= ?n1 (+ 1 ?n2))
(= (+ ?bal ?n2) (+ 1 ?n1))
(= ?n_80 ?n)
(tobool (ssep 
(pto ?in (sref (ref ele ?Anon_14) (ref height ?n_80) (ref left ?p) (ref right ?q) ))
(avl ?p ?m1 ?n1 ?Anon_15)
(avl ?q ?m2 ?n2 ?Anon_16)
) )
)))))






































































































































































































































































































































(declare-fun tprm () node)
(declare-fun Anon137 () Int)
(declare-fun ss9 () node)
(declare-fun ss8 () node)
(declare-fun v73prm () Int)
(declare-fun b19 () Int)
(declare-fun Anon139 () Int)
(declare-fun n49 () Int)
(declare-fun m39 () Int)
(declare-fun v71prm () Int)
(declare-fun b18 () Int)
(declare-fun Anon138 () Int)
(declare-fun n46 () Int)
(declare-fun m36 () Int)
(declare-fun t17 () Int)
(declare-fun t18 () Int)
(declare-fun h12 () Int)
(declare-fun h13 () Int)
(declare-fun h14 () Int)
(declare-fun t19 () Int)
(declare-fun flted24 () Int)
(declare-fun flted25 () Int)
(declare-fun Anon39 () Int)
(declare-fun Anon104 () Int)
(declare-fun cn () Int)
(declare-fun cm () Int)
(declare-fun Anon38 () Int)
(declare-fun Anon105 () Int)
(declare-fun bn () Int)
(declare-fun bm () Int)
(declare-fun c () node)
(declare-fun q8 () node)
(declare-fun b11 () node)
(declare-fun p8 () node)
(declare-fun Anon37 () Int)
(declare-fun Anon36 () node)
(declare-fun Anon106 () node)
(declare-fun m26 () Int)
(declare-fun m25 () Int)
(declare-fun n31 () Int)
(declare-fun n32 () Int)
(declare-fun n33 () Int)
(declare-fun tm () Int)
(declare-fun b () Int)
(declare-fun tn () Int)
(declare-fun tmpprm () node)
(declare-fun xprm () NUM)
(declare-fun x () NUM)
(declare-fun t8 () node)
(declare-fun t6 () node)
(declare-fun m17 () Int)
(declare-fun n20 () Int)
(declare-fun Anon95 () Int)
(declare-fun tm1 () Int)
(declare-fun tn1 () Int)
(declare-fun b6 () Int)
(declare-fun left3 () node)
(declare-fun p5 () node)
(declare-fun flted8 () Int)
(declare-fun resn9 () Int)
(declare-fun resb1 () Int)
(declare-fun m () Int)
(declare-fun b7 () Int)
(declare-fun m16 () Int)
(declare-fun n19 () Int)
(declare-fun Anon96 () Int)
(declare-fun n () Int)
(declare-fun m22 () Int)
(declare-fun n27 () Int)
(declare-fun Anon102 () Int)
(declare-fun m21 () Int)
(declare-fun n28 () Int)
(declare-fun Anon103 () Int)
(declare-fun m24 () Int)
(declare-fun n30 () Int)
(declare-fun b10 () Int)
(declare-fun Anon30 () NUM)
(declare-fun Anon97 () NUM)
(declare-fun Anon31 () Int)
(declare-fun n21 () Int)
(declare-fun k1 () node)
(declare-fun v12 () node)
(declare-fun d () node)
(declare-fun q5 () node)
(declare-fun dm () Int)
(declare-fun m18 () Int)
(declare-fun dn () Int)
(declare-fun n22 () Int)
(declare-fun Anon32 () Int)
(declare-fun b8 () Int)
(declare-fun Anon33 () node)
(declare-fun Anon101 () node)
(declare-fun Anon34 () Int)
(declare-fun n26 () Int)
(declare-fun a () node)
(declare-fun p7 () node)
(declare-fun k2 () node)
(declare-fun q7 () node)
(declare-fun am () Int)
(declare-fun m23 () Int)
(declare-fun an () Int)
(declare-fun n29 () Int)
(declare-fun Anon35 () Int)
(declare-fun b9 () Int)


(assert 
(and 
;lexvar(<= b19 2)
(<= 0 b19)
(<= 0 n49)
(<= 0 m39)
(= v73prm n49)
(<= Anon139 2)
(<= 0 Anon139)
(<= 0 h13)
(<= 0 flted24)
(= b19 Anon139)
(= n49 h13)
(= m39 flted24)
(<= b18 2)
(<= 0 b18)
(<= 0 n46)
(<= 0 m36)
(= v71prm n46)
(<= Anon138 2)
(<= 0 Anon138)
(<= 0 h12)
(<= 0 flted25)
(= b18 Anon138)
(= n46 h12)
(= m36 flted25)
(<= Anon39 2)
(<= 0 Anon39)
(<= 0 cn)
(<= 0 cm)
(<= Anon38 2)
(<= 0 Anon38)
(<= 0 bn)
(<= 0 bm)
(<= Anon35 2)
(<= 0 Anon35)
(<= 0 an)
(<= 0 am)
(<= Anon32 2)
(<= 0 Anon32)
(<= 0 dn)
(<= 0 dm)
;eqmax(= h13 (+ t17 1))
;eqmax(= h12 (+ t18 1))
;eqmax(= h14 (+ t19 1))
(= flted24 (+ (+ 1 cm) dm))
(= flted25 (+ (+ 1 am) bm))
(distinct t8 nil)
(<= b8 2)
(<= 0 b8)
(<= 0 n22)
(<= 0 m18)
(distinct v12 nil)
(<= b9 2)
(<= 0 b9)
(<= 0 n29)
(<= 0 m23)
(distinct q7 nil)
(<= Anon105 2)
(<= 0 Anon105)
(<= 0 n32)
(<= 0 m26)
(<= Anon104 2)
(<= 0 Anon104)
(<= 0 n31)
(<= 0 m25)
(= Anon39 Anon104)
(= cn n31)
(= cm m25)
(= Anon38 Anon105)
(= bn n32)
(= bm m26)
(= c q8)
(= b11 p8)
(= Anon37 n33)
(= Anon36 Anon106)
(= m24 (+ (+ m25 1) m26))
(<= (+ 0 n31) (+ n32 1))
(<= n32 (+ 1 n31))
(= (+ b10 n31) (+ 1 n32))
(= n33 n30)
(<= n29 n30)
(= m (+ (+ m21 1) m22))
(<= (+ 0 n28) (+ n27 1))
(<= n27 (+ 1 n28))
(= (+ b7 n28) (+ 1 n27))
(= n26 n)
(< xprm Anon97)
(= tm (+ (+ m16 1) m17))
(<= (+ 0 n19) (+ n20 1))
(<= n20 (+ 1 n19))
(= (+ b n19) (+ 1 n20))
(= n21 tn)
(= tmpprm nil)
(= xprm x)
(= t8 t6)
(= tm1 m17)
(= tn1 n20)
(= b6 Anon95)
(<= 0 m17)
(<= 0 n20)
(<= 0 Anon95)
(<= Anon95 2)
(= flted8 (+ 1 tm1))
(distinct p5 nil)
(< 0 tm1)
(< 0 tn1)
(<= 0 tm1)
(<= 0 tn1)
(<= 0 b6)
(<= b6 2)
(= left3 p5)
(= m flted8)
(= n resn9)
(= b7 resb1)
(<= 0 flted8)
(<= 0 resn9)
(<= 0 resb1)
(<= resb1 2)
(<= 0 m)
(<= 0 n)
(<= 0 b7)
(<= b7 2)
(= m18 m16)
(= n22 n19)
(= b8 Anon96)
(<= 0 m16)
(<= 0 n19)
(<= 0 Anon96)
(<= Anon96 2)
(= (+ 2 n22) n)
(= m23 m22)
(= n29 n27)
(= b9 Anon102)
(<= 0 m22)
(<= 0 n27)
(<= 0 Anon102)
(<= Anon102 2)
(= m24 m21)
(= n30 n28)
(= b10 Anon103)
(<= 0 m21)
(<= 0 n28)
(<= 0 Anon103)
(<= Anon103 2)
(<= 0 m24)
(<= 0 n30)
(<= 0 b10)
(<= b10 2)
(= Anon30 Anon97)
(= Anon31 n21)
(= k1 v12)
(= d q5)
(= dm m18)
(= dn n22)
(= Anon32 b8)
(= Anon33 Anon101)
(= Anon34 n26)
(= a p7)
(= k2 q7)
(= am m23)
(= an n29)
(= Anon35 b9)
(tobool (ssep 
(pto tprm (sref (ref ele Anon137) (ref height h14) (ref left ss9) (ref right ss8) ))
(avl ss9 m36 n46 b18)
(avl ss8 m39 n49 b19)
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