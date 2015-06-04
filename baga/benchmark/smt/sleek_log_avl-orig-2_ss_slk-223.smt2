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
(declare-fun Anon148 () Int)
(declare-fun Anon149 () Int)
(declare-fun ss10 () node)
(declare-fun Anon150 () Int)
(declare-fun v70prm () node)
(declare-fun ss11 () node)
(declare-fun t20 () Int)
(declare-fun t21 () Int)
(declare-fun h15 () Int)
(declare-fun h16 () Int)
(declare-fun h17 () Int)
(declare-fun t22 () Int)
(declare-fun flted26 () Int)
(declare-fun flted27 () Int)
(declare-fun Anon70 () Int)
(declare-fun Anon113 () Int)
(declare-fun cn () Int)
(declare-fun cm () Int)
(declare-fun Anon69 () Int)
(declare-fun Anon114 () Int)
(declare-fun bn () Int)
(declare-fun bm () Int)
(declare-fun c () node)
(declare-fun q11 () node)
(declare-fun b17 () node)
(declare-fun p11 () node)
(declare-fun Anon68 () Int)
(declare-fun Anon67 () node)
(declare-fun Anon115 () node)
(declare-fun m35 () Int)
(declare-fun m34 () Int)
(declare-fun n43 () Int)
(declare-fun n44 () Int)
(declare-fun n45 () Int)
(declare-fun tm () Int)
(declare-fun b () Int)
(declare-fun tn () Int)
(declare-fun tmpprm () node)
(declare-fun xprm () NUM)
(declare-fun x () NUM)
(declare-fun t13 () node)
(declare-fun t6 () node)
(declare-fun m16 () Int)
(declare-fun n19 () Int)
(declare-fun Anon96 () Int)
(declare-fun tm2 () Int)
(declare-fun tn2 () Int)
(declare-fun b12 () Int)
(declare-fun right3 () node)
(declare-fun q5 () node)
(declare-fun flted16 () Int)
(declare-fun resn11 () Int)
(declare-fun resb3 () Int)
(declare-fun m () Int)
(declare-fun b13 () Int)
(declare-fun m17 () Int)
(declare-fun n20 () Int)
(declare-fun Anon95 () Int)
(declare-fun n () Int)
(declare-fun m30 () Int)
(declare-fun n40 () Int)
(declare-fun Anon112 () Int)
(declare-fun m31 () Int)
(declare-fun n39 () Int)
(declare-fun Anon111 () Int)
(declare-fun m33 () Int)
(declare-fun n42 () Int)
(declare-fun b16 () Int)
(declare-fun Anon61 () NUM)
(declare-fun Anon97 () NUM)
(declare-fun Anon62 () Int)
(declare-fun n21 () Int)
(declare-fun a () node)
(declare-fun p5 () node)
(declare-fun k2 () node)
(declare-fun v16 () node)
(declare-fun am () Int)
(declare-fun m27 () Int)
(declare-fun an () Int)
(declare-fun n34 () Int)
(declare-fun Anon63 () Int)
(declare-fun b14 () Int)
(declare-fun Anon64 () node)
(declare-fun Anon110 () node)
(declare-fun Anon65 () Int)
(declare-fun n38 () Int)
(declare-fun k3 () node)
(declare-fun p10 () node)
(declare-fun d () node)
(declare-fun q10 () node)
(declare-fun dm () Int)
(declare-fun m32 () Int)
(declare-fun dn () Int)
(declare-fun n41 () Int)
(declare-fun Anon66 () Int)
(declare-fun b15 () Int)


(assert 
(and 
;lexvar(= v70prm ss11)
(<= Anon70 2)
(<= 0 Anon70)
(<= 0 cn)
(<= 0 cm)
(<= Anon69 2)
(<= 0 Anon69)
(<= 0 bn)
(<= 0 bm)
(<= Anon66 2)
(<= 0 Anon66)
(<= 0 dn)
(<= 0 dm)
(<= Anon63 2)
(<= 0 Anon63)
(<= 0 an)
(<= 0 am)
;eqmax(= h16 (+ t20 1))
;eqmax(= h15 (+ t21 1))
;eqmax(= h17 (+ t22 1))
(= flted26 (+ (+ 1 cm) dm))
(= flted27 (+ (+ 1 am) bm))
(distinct t13 nil)
(<= b14 2)
(<= 0 b14)
(<= 0 n34)
(<= 0 m27)
(distinct v16 nil)
(<= b15 2)
(<= 0 b15)
(<= 0 n41)
(<= 0 m32)
(distinct p10 nil)
(<= Anon114 2)
(<= 0 Anon114)
(<= 0 n44)
(<= 0 m35)
(<= Anon113 2)
(<= 0 Anon113)
(<= 0 n43)
(<= 0 m34)
(= Anon70 Anon113)
(= cn n43)
(= cm m34)
(= Anon69 Anon114)
(= bn n44)
(= bm m35)
(= c q11)
(= b17 p11)
(= Anon68 n45)
(= Anon67 Anon115)
(= m33 (+ (+ m34 1) m35))
(<= (+ 0 n43) (+ n44 1))
(<= n44 (+ 1 n43))
(= (+ b16 n43) (+ 1 n44))
(= n45 n42)
(<= n41 n42)
(= m (+ (+ m30 1) m31))
(<= (+ 0 n40) (+ n39 1))
(<= n39 (+ 1 n40))
(= (+ b13 n40) (+ 1 n39))
(= n38 n)
(<= Anon97 xprm)
(= tm (+ (+ m16 1) m17))
(<= (+ 0 n19) (+ n20 1))
(<= n20 (+ 1 n19))
(= (+ b n19) (+ 1 n20))
(= n21 tn)
(= tmpprm nil)
(= xprm x)
(= t13 t6)
(= tm2 m16)
(= tn2 n19)
(= b12 Anon96)
(<= 0 m16)
(<= 0 n19)
(<= 0 Anon96)
(<= Anon96 2)
(= flted16 (+ 1 tm2))
(distinct q5 nil)
(< 0 tm2)
(< 0 tn2)
(<= 0 tm2)
(<= 0 tn2)
(<= 0 b12)
(<= b12 2)
(= right3 q5)
(= m flted16)
(= n resn11)
(= b13 resb3)
(<= 0 flted16)
(<= 0 resn11)
(<= 0 resb3)
(<= resb3 2)
(<= 0 m)
(<= 0 n)
(<= 0 b13)
(<= b13 2)
(= m27 m17)
(= n34 n20)
(= b14 Anon95)
(<= 0 m17)
(<= 0 n20)
(<= 0 Anon95)
(<= Anon95 2)
(= (+ 2 n34) n)
(= m32 m30)
(= n41 n40)
(= b15 Anon112)
(<= 0 m30)
(<= 0 n40)
(<= 0 Anon112)
(<= Anon112 2)
(= m33 m31)
(= n42 n39)
(= b16 Anon111)
(<= 0 m31)
(<= 0 n39)
(<= 0 Anon111)
(<= Anon111 2)
(<= 0 m33)
(<= 0 n42)
(<= 0 b16)
(<= b16 2)
(= Anon61 Anon97)
(= Anon62 n21)
(= a p5)
(= k2 v16)
(= am m27)
(= an n34)
(= Anon63 b14)
(= Anon64 Anon110)
(= Anon65 n38)
(= k3 p10)
(= d q10)
(= dm m32)
(= dn n41)
(= Anon66 b15)
(tobool (ssep 
(pto tprm (sref (ref ele Anon148) (ref height h17) (ref left ss11) (ref right ss10) ))
(avl ss11 flted27 h15 Anon149)
(avl ss10 flted26 h16 Anon150)
) )
)
)

(assert (not 
(and 
(tobool  
(avl v70prm m36 n46 b18)
 )
)
))

(check-sat)