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






































































































































































































































































































































(declare-fun Anon53_7884 () Int)
(declare-fun resl4_7885 () node)
(declare-fun Anon54_7886 () Int)
(declare-fun resr4_7887 () node)
(declare-fun Anon55_7888 () Int)
(declare-fun resrl1_7889 () node)
(declare-fun Anon56_7890 () Int)
(declare-fun resrr1_7891 () node)
(declare-fun Anon57_7892 () Int)
(declare-fun Anon52 () Int)
(declare-fun n13 () Int)
(declare-fun m10 () Int)
(declare-fun Anon51 () Int)
(declare-fun n12 () Int)
(declare-fun m11 () Int)
(declare-fun q2 () node)
(declare-fun reslr2 () node)
(declare-fun p2 () node)
(declare-fun resll2 () node)
(declare-fun Anon50 () node)
(declare-fun Anon46 () node)
(declare-fun k3 () node)
(declare-fun Anon18 () node)
(declare-fun Anon33 () node)
(declare-fun Anon19 () node)
(declare-fun Anon34 () node)
(declare-fun l () node)
(declare-fun a () node)
(declare-fun r () node)
(declare-fun Anon21 () node)
(declare-fun Anon36 () node)
(declare-fun Anon22 () node)
(declare-fun Anon37 () node)
(declare-fun rl () node)
(declare-fun b () node)
(declare-fun rr () node)
(declare-fun c () node)
(declare-fun k2 () node)
(declare-fun tmp7 () Int)
(declare-fun tmp6 () Int)
(declare-fun resln2 () Int)
(declare-fun Anon20 () Int)
(declare-fun Anon23 () Int)
(declare-fun Anon24 () Int)
(declare-fun left2 () node)
(declare-fun k1 () node)
(declare-fun Anon6 () node)
(declare-fun Anon30 () node)
(declare-fun Anon7 () node)
(declare-fun Anon31 () node)
(declare-fun l1 () node)
(declare-fun r1 () node)
(declare-fun d () node)
(declare-fun Anon9 () node)
(declare-fun Anon45 () node)
(declare-fun Anon10 () Int)
(declare-fun resn3 () Int)
(declare-fun ll () node)
(declare-fun lr () node)
(declare-fun resr3 () node)
(declare-fun cm3 () Int)
(declare-fun cn3 () Int)
(declare-fun Anon47 () Int)
(declare-fun bm3 () Int)
(declare-fun bn3 () Int)
(declare-fun Anon49 () Int)
(declare-fun am3 () Int)
(declare-fun an3 () Int)
(declare-fun Anon48 () Int)
(declare-fun resl3 () node)
(declare-fun v8 () node)
(declare-fun k3prm () node)
(declare-fun tmp8_7893 () Int)
(declare-fun resn4_7894 () Int)
(declare-fun tmp9_7895 () Int)
(declare-fun resrn1_7896 () Int)
(declare-fun cm4 () Int)
(declare-fun cn4 () Int)
(declare-fun Anon8 () Int)
(declare-fun am4 () Int)
(declare-fun an4 () Int)
(declare-fun Anon11 () Int)
(declare-fun bm4 () Int)
(declare-fun bn4 () Int)
(declare-fun Anon12 () Int)
(declare-fun res () node)
(declare-fun Anon39 () Int)
(declare-fun cn () Int)
(declare-fun cm () Int)
(declare-fun Anon38 () Int)
(declare-fun bn () Int)
(declare-fun bm () Int)
(declare-fun Anon35 () Int)
(declare-fun an () Int)
(declare-fun am () Int)
(declare-fun Anon32 () Int)
(declare-fun dn () Int)
(declare-fun dm () Int)


(assert 
(exists ((Anon53 Int)(resl4 node)(Anon54 Int)(resr4 node)(Anon55 Int)(resrl1 node)(Anon56 Int)(resrr1 node)(Anon57 Int)(tmp8 Int)(resn4 Int)(tmp9 Int)(resrn1 Int))(and 
;lexvar(= am4 (+ (+ m10 1) m11))
(= (+ Anon11 n13) (+ 1 n12))
(= resln2 an4)
(<= (+ 0 n13) (+ n12 1))
(<= n12 (+ 1 n13))
(= Anon52 Anon49)
(= n13 bn3)
(= m10 bm3)
(= Anon51 Anon48)
(= n12 an3)
(= m11 am3)
(= q2 reslr2)
(= p2 resll2)
(= Anon50 Anon46)
(<= dn (+ cn 1))
(<= cn (+ dn 1))
(<= an (+ bn 1))
(<= bn (+ an 1))
(= k3prm k3)
(= Anon18 Anon33)
(= Anon19 Anon34)
(= l a)
(= r k2)
(= am3 am)
(= an3 an)
(= Anon20 Anon35)
(= Anon21 Anon36)
(= Anon22 Anon37)
(= rl b)
(= rr c)
(= bm3 bm)
(= bn3 bn)
(= Anon23 Anon38)
(= cm3 cm)
(= cn3 cn)
(= Anon24 Anon39)
(<= 0 cm)
(<= 0 cn)
(<= 0 Anon39)
(<= Anon39 2)
(<= 0 bm)
(<= 0 bn)
(<= 0 Anon38)
(<= Anon38 2)
(distinct k2 nil)
(<= 0 am)
(<= 0 an)
(<= 0 Anon35)
(<= Anon35 2)
(distinct k1 nil)
(= resln2 (+ 1 tmp7))
;eqmax(= resn3 (+ 1 tmp6))
;eqmax(<= 0 Anon20)
(<= Anon20 2)
(<= 0 Anon23)
(<= Anon23 2)
(<= 0 Anon24)
(<= Anon24 2)
(= left2 k1)
(= Anon6 Anon30)
(= Anon7 Anon31)
(= l1 v8)
(= r1 d)
(= cm4 dm)
(= cn4 dn)
(= Anon8 Anon32)
(= Anon9 Anon45)
(= Anon10 resn3)
(= ll resl3)
(= lr resr3)
(= bm4 cm3)
(= bn4 cn3)
(= Anon12 Anon47)
(<= 0 cm3)
(<= 0 cn3)
(<= 0 Anon47)
(<= Anon47 2)
(<= 0 bm3)
(<= 0 bn3)
(<= 0 Anon49)
(<= Anon49 2)
(<= 0 am3)
(<= 0 an3)
(<= 0 Anon48)
(<= Anon48 2)
(distinct resl3 nil)
(distinct v8 nil)
(<= 0 dm)
(<= 0 dn)
(<= 0 Anon32)
(<= Anon32 2)
(distinct k3prm nil)
(= resrn1 (+ 1 tmp8))
;eqmax(= resn4 (+ 1 tmp9))
;eqmax(<= 0 cm4)
(<= 0 cn4)
(<= 0 Anon8)
(<= Anon8 2)
(<= 0 am4)
(<= 0 an4)
(<= 0 Anon11)
(<= Anon11 2)
(<= 0 bm4)
(<= 0 bn4)
(<= 0 Anon12)
(<= Anon12 2)
(tobool (ssep 
(pto res (sref (ref ele Anon53) (ref height resn4) (ref left resl4) (ref right resr4) ))
(avl resl4 am4 an4 Anon54)
(pto resr4 (sref (ref ele Anon55) (ref height resrn1) (ref left resrl1) (ref right resrr1) ))
(avl resrl1 bm4 bn4 Anon56)
(avl resrr1 cm4 cn4 Anon57)
) )
))
)

(assert (not 
(exists ((flted Int)(flted1 Int)(Anon58 Int)(ss node)(Anon59 Int)(ss1 node)(Anon60 Int)(h Int)(t Int)(h1 Int)(t1 NUM)(h2 Int)(t2 NUM))(and 
;eqmax(= h2 (+ t2 1))
;eqmax(= h1 (+ t1 1))
;eqmax(= h (+ t 1))
(= flted (+ (+ 1 cm) dm))
(= flted1 (+ (+ 1 am) bm))
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
(tobool (ssep 
(pto res (sref (ref ele Anon58) (ref height h) (ref left ss) (ref right ss1) ))
(avl ss flted1 h1 Anon59)
(avl ss1 flted h2 Anon60)
) )
))
))

(check-sat)