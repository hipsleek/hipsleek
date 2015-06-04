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
(declare-fun Anon140 () Int)
(declare-fun resr11 () node)
(declare-fun v76prm () Int)
(declare-fun b19 () Int)
(declare-fun Anon142 () Int)
(declare-fun n49 () Int)
(declare-fun m39 () Int)
(declare-fun resl11 () node)
(declare-fun resn15 () Int)
(declare-fun tmp22 () Int)
(declare-fun tmp23 () Int)
(declare-fun Anon24 () Int)
(declare-fun cn () Int)
(declare-fun cm () Int)
(declare-fun Anon23 () Int)
(declare-fun rr () node)
(declare-fun q10 () node)
(declare-fun rl () node)
(declare-fun p10 () node)
(declare-fun Anon22 () Int)
(declare-fun Anon21 () node)
(declare-fun Anon110 () node)
(declare-fun Anon20 () Int)
(declare-fun r () node)
(declare-fun v16 () node)
(declare-fun l () node)
(declare-fun p5 () node)
(declare-fun Anon19 () Int)
(declare-fun Anon18 () NUM)
(declare-fun b16 () Int)
(declare-fun Anon111 () Int)
(declare-fun m33 () Int)
(declare-fun b15 () Int)
(declare-fun Anon112 () Int)
(declare-fun m32 () Int)
(declare-fun b14 () Int)
(declare-fun Anon95 () Int)
(declare-fun n34 () Int)
(declare-fun m27 () Int)
(declare-fun right3 () node)
(declare-fun resn11 () Int)
(declare-fun resb3 () Int)
(declare-fun q5 () node)
(declare-fun flted16 () Int)
(declare-fun b12 () Int)
(declare-fun Anon96 () Int)
(declare-fun tn2 () Int)
(declare-fun tm2 () Int)
(declare-fun t12 () node)
(declare-fun t6 () node)
(declare-fun x () NUM)
(declare-fun tmpprm () node)
(declare-fun n21 () Int)
(declare-fun b () Int)
(declare-fun tn () Int)
(declare-fun n20 () Int)
(declare-fun n19 () Int)
(declare-fun tm () Int)
(declare-fun m17 () Int)
(declare-fun m16 () Int)
(declare-fun Anon97 () NUM)
(declare-fun xprm () NUM)
(declare-fun n38 () Int)
(declare-fun b13 () Int)
(declare-fun n () Int)
(declare-fun n39 () Int)
(declare-fun n40 () Int)
(declare-fun m () Int)
(declare-fun m31 () Int)
(declare-fun m30 () Int)
(declare-fun n42 () Int)
(declare-fun n41 () Int)
(declare-fun Anon145 () node)
(declare-fun Anon141 () node)
(declare-fun p12 () node)
(declare-fun resll5 () node)
(declare-fun q12 () node)
(declare-fun reslr5 () node)
(declare-fun am () Int)
(declare-fun an () Int)
(declare-fun Anon146 () Int)
(declare-fun Anon143 () Int)
(declare-fun bm () Int)
(declare-fun bn () Int)
(declare-fun Anon147 () Int)
(declare-fun Anon144 () Int)
(declare-fun resln5 () Int)
(declare-fun b18 () Int)
(declare-fun n46 () Int)
(declare-fun n47 () Int)
(declare-fun n48 () Int)
(declare-fun m36 () Int)
(declare-fun m38 () Int)
(declare-fun m37 () Int)


(assert 
(and 
;lexvar(= v76prm (+ 1 n46))
(<= n49 n46)
(<= b19 2)
(<= 0 b19)
(<= 0 n49)
(<= 0 m39)
(<= Anon142 2)
(<= 0 Anon142)
(<= 0 cn)
(<= 0 cm)
(= b19 Anon142)
(= n49 cn)
(= m39 cm)
(<= b18 2)
(<= 0 b18)
(<= 0 n46)
(<= 0 m36)
(distinct resl11 nil)
(<= Anon143 2)
(<= 0 Anon143)
(<= 0 an)
(<= 0 am)
(<= Anon144 2)
(<= 0 Anon144)
(<= 0 bn)
(<= 0 bm)
(<= Anon24 2)
(<= 0 Anon24)
(<= Anon23 2)
(<= 0 Anon23)
(<= Anon20 2)
(<= 0 Anon20)
;eqmax(= resn15 (+ 1 tmp22))
;eqmax(= resln5 (+ 1 tmp23))
(distinct t12 nil)
(<= b14 2)
(<= 0 b14)
(<= 0 n34)
(<= 0 m27)
(distinct v16 nil)
(<= b16 2)
(<= 0 b16)
(<= 0 n42)
(<= 0 m33)
(<= b15 2)
(<= 0 b15)
(<= 0 n41)
(<= 0 m32)
(= Anon24 b15)
(= cn n41)
(= cm m32)
(= Anon23 b16)
(= bn n42)
(= bm m33)
(= rr q10)
(= rl p10)
(= Anon22 n38)
(= Anon21 Anon110)
(= Anon20 b14)
(= an n34)
(= am m27)
(= r v16)
(= l p5)
(= Anon19 n21)
(= Anon18 Anon97)
(<= Anon111 2)
(<= 0 Anon111)
(<= 0 n39)
(<= 0 m31)
(= b16 Anon111)
(= n42 n39)
(= m33 m31)
(<= Anon112 2)
(<= 0 Anon112)
(<= 0 n40)
(<= 0 m30)
(= b15 Anon112)
(= n41 n40)
(= m32 m30)
(= (+ 2 n34) n)
(<= Anon95 2)
(<= 0 Anon95)
(<= 0 n20)
(<= 0 m17)
(= b14 Anon95)
(= n34 n20)
(= m27 m17)
(<= b13 2)
(<= 0 b13)
(<= 0 n)
(<= 0 m)
(<= resb3 2)
(<= 0 resb3)
(<= 0 resn11)
(<= 0 flted16)
(= b13 resb3)
(= n resn11)
(= m flted16)
(= right3 q5)
(<= b12 2)
(<= 0 b12)
(<= 0 tn2)
(<= 0 tm2)
(< 0 tn2)
(< 0 tm2)
(distinct q5 nil)
(= flted16 (+ 1 tm2))
(<= Anon96 2)
(<= 0 Anon96)
(<= 0 n19)
(<= 0 m16)
(= b12 Anon96)
(= tn2 n19)
(= tm2 m16)
(= t12 t6)
(= xprm x)
(= tmpprm nil)
(= n21 tn)
(= (+ b n19) (+ 1 n20))
(<= n20 (+ 1 n19))
(<= (+ 0 n19) (+ n20 1))
(= tm (+ (+ m16 1) m17))
(<= Anon97 xprm)
(= n38 n)
(= (+ b13 n40) (+ 1 n39))
(<= n39 (+ 1 n40))
(<= (+ 0 n40) (+ n39 1))
(= m (+ (+ m30 1) m31))
(< n42 n41)
(= Anon145 Anon141)
(= p12 resll5)
(= q12 reslr5)
(= m38 am)
(= n47 an)
(= Anon146 Anon143)
(= m37 bm)
(= n48 bn)
(= Anon147 Anon144)
(<= n47 (+ 1 n48))
(<= (+ 0 n48) (+ n47 1))
(= resln5 n46)
(= (+ b18 n48) (+ 1 n47))
(= m36 (+ (+ m37 1) m38))
(tobool (ssep 
(pto tprm (sref (ref ele Anon140) (ref height resn15) (ref left resl11) (ref right resr11) ))
(avl resl11 m36 n46 b18)
(avl resr11 m39 n49 b19)
) )
)
)

(assert (not 
(and 
(tobool  
(pto tprm (sref (ref ele ele44prm) (ref height height44prm) (ref left left44prm) (ref right right44prm) ))
 )
)
))

(check-sat)