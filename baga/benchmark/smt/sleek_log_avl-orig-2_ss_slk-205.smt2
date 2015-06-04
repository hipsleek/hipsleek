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
(declare-fun Anon116_18416 () Int)
(declare-fun resl8_18417 () node)
(declare-fun Anon117_18418 () Int)
(declare-fun resr8_18419 () node)
(declare-fun Anon118_18420 () Int)
(declare-fun resrl4_18421 () node)
(declare-fun Anon119_18422 () Int)
(declare-fun resrr4_18423 () node)
(declare-fun Anon120_18424 () Int)
(declare-fun resn12_18426 () Int)
(declare-fun tmp17_18427 () Int)
(declare-fun resrn4_18428 () Int)
(declare-fun tmp16_18425 () Int)
(declare-fun Anon12 () Int)
(declare-fun bn () Int)
(declare-fun bm () Int)
(declare-fun Anon11 () Int)
(declare-fun an () Int)
(declare-fun am () Int)
(declare-fun lr () node)
(declare-fun q7 () node)
(declare-fun ll () node)
(declare-fun p7 () node)
(declare-fun Anon10 () Int)
(declare-fun Anon9 () node)
(declare-fun Anon101 () node)
(declare-fun Anon8 () Int)
(declare-fun cn () Int)
(declare-fun cm () Int)
(declare-fun r () node)
(declare-fun q5 () node)
(declare-fun l () node)
(declare-fun v12 () node)
(declare-fun Anon7 () Int)
(declare-fun Anon6 () NUM)
(declare-fun b10 () Int)
(declare-fun Anon103 () Int)
(declare-fun m24 () Int)
(declare-fun b9 () Int)
(declare-fun Anon102 () Int)
(declare-fun m23 () Int)
(declare-fun b8 () Int)
(declare-fun Anon96 () Int)
(declare-fun n22 () Int)
(declare-fun m18 () Int)
(declare-fun left3 () node)
(declare-fun resn9 () Int)
(declare-fun resb1 () Int)
(declare-fun p5 () node)
(declare-fun flted8 () Int)
(declare-fun b6 () Int)
(declare-fun Anon95 () Int)
(declare-fun tn1 () Int)
(declare-fun tm1 () Int)
(declare-fun t7 () node)
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
(declare-fun xprm () NUM)
(declare-fun Anon97 () NUM)
(declare-fun n26 () Int)
(declare-fun b7 () Int)
(declare-fun n () Int)
(declare-fun n27 () Int)
(declare-fun n28 () Int)
(declare-fun m () Int)
(declare-fun m22 () Int)
(declare-fun m21 () Int)
(declare-fun n30 () Int)
(declare-fun n29 () Int)


(assert 
(exists ((Anon116 Int)(resl8 node)(Anon117 Int)(resr8 node)(Anon118 Int)(resrl4 node)(Anon119 Int)(resrr4 node)(Anon120 Int)(tmp16 Int)(resn12 Int)(tmp17 Int)(resrn4 Int))(and 
;lexvar(<= Anon12 2)
(<= 0 Anon12)
(<= 0 bn)
(<= 0 bm)
(<= Anon11 2)
(<= 0 Anon11)
(<= 0 an)
(<= 0 am)
(<= Anon8 2)
(<= 0 Anon8)
(<= 0 cn)
(<= 0 cm)
;eqmax(= resn12 (+ 1 tmp17))
;eqmax(= resrn4 (+ 1 tmp16))
(distinct t7 nil)
(<= b8 2)
(<= 0 b8)
(<= 0 n22)
(<= 0 m18)
(distinct v12 nil)
(<= b9 2)
(<= 0 b9)
(<= 0 n29)
(<= 0 m23)
(<= b10 2)
(<= 0 b10)
(<= 0 n30)
(<= 0 m24)
(= Anon12 b10)
(= bn n30)
(= bm m24)
(= Anon11 b9)
(= an n29)
(= am m23)
(= lr q7)
(= ll p7)
(= Anon10 n26)
(= Anon9 Anon101)
(= Anon8 b8)
(= cn n22)
(= cm m18)
(= r q5)
(= l v12)
(= Anon7 n21)
(= Anon6 Anon97)
(<= Anon103 2)
(<= 0 Anon103)
(<= 0 n28)
(<= 0 m21)
(= b10 Anon103)
(= n30 n28)
(= m24 m21)
(<= Anon102 2)
(<= 0 Anon102)
(<= 0 n27)
(<= 0 m22)
(= b9 Anon102)
(= n29 n27)
(= m23 m22)
(= (+ 2 n22) n)
(<= Anon96 2)
(<= 0 Anon96)
(<= 0 n19)
(<= 0 m16)
(= b8 Anon96)
(= n22 n19)
(= m18 m16)
(<= b7 2)
(<= 0 b7)
(<= 0 n)
(<= 0 m)
(<= resb1 2)
(<= 0 resb1)
(<= 0 resn9)
(<= 0 flted8)
(= b7 resb1)
(= n resn9)
(= m flted8)
(= left3 p5)
(<= b6 2)
(<= 0 b6)
(<= 0 tn1)
(<= 0 tm1)
(< 0 tn1)
(< 0 tm1)
(distinct p5 nil)
(= flted8 (+ 1 tm1))
(<= Anon95 2)
(<= 0 Anon95)
(<= 0 n20)
(<= 0 m17)
(= b6 Anon95)
(= tn1 n20)
(= tm1 m17)
(= t7 t6)
(= xprm x)
(= tmpprm nil)
(= n21 tn)
(= (+ b n19) (+ 1 n20))
(<= n20 (+ 1 n19))
(<= (+ 0 n19) (+ n20 1))
(= tm (+ (+ m16 1) m17))
(< xprm Anon97)
(= n26 n)
(= (+ b7 n28) (+ 1 n27))
(<= n27 (+ 1 n28))
(<= (+ 0 n28) (+ n27 1))
(= m (+ (+ m21 1) m22))
(< n30 n29)
(tobool (ssep 
(pto tprm (sref (ref ele Anon116) (ref height resn12) (ref left resl8) (ref right resr8) ))
(avl resl8 am an Anon117)
(pto resr8 (sref (ref ele Anon118) (ref height resrn4) (ref left resrl4) (ref right resrr4) ))
(avl resrl4 bm bn Anon119)
(avl resrr4 cm cn Anon120)
) )
))
)

(assert (not 
(and 
(tobool  
(pto tprm (sref (ref ele ele42prm) (ref height height42prm) (ref left left42prm) (ref right right42prm) ))
 )
)
))

(check-sat)