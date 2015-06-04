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






































































































































































































































































































































(declare-fun Anon84_8867 () Int)
(declare-fun resl7_8868 () node)
(declare-fun Anon85_8869 () Int)
(declare-fun resr7_8870 () node)
(declare-fun Anon86_8871 () Int)
(declare-fun resll3_8872 () node)
(declare-fun Anon87_8873 () Int)
(declare-fun reslr3_8874 () node)
(declare-fun Anon88_8875 () Int)
(declare-fun Anon83 () Int)
(declare-fun n15 () Int)
(declare-fun m12 () Int)
(declare-fun Anon82 () Int)
(declare-fun n14 () Int)
(declare-fun m13 () Int)
(declare-fun q3 () node)
(declare-fun resrr3 () node)
(declare-fun p3 () node)
(declare-fun resrl3 () node)
(declare-fun Anon81 () node)
(declare-fun Anon78 () node)
(declare-fun k1 () node)
(declare-fun Anon6 () node)
(declare-fun Anon64 () node)
(declare-fun Anon7 () node)
(declare-fun Anon65 () node)
(declare-fun l () node)
(declare-fun r () node)
(declare-fun d () node)
(declare-fun Anon9 () node)
(declare-fun Anon67 () node)
(declare-fun Anon10 () node)
(declare-fun Anon68 () node)
(declare-fun ll () node)
(declare-fun b () node)
(declare-fun lr () node)
(declare-fun c () node)
(declare-fun k3 () node)
(declare-fun tmp13 () Int)
(declare-fun tmp12 () Int)
(declare-fun resrn3 () Int)
(declare-fun Anon8 () Int)
(declare-fun Anon11 () Int)
(declare-fun Anon12 () Int)
(declare-fun right2 () node)
(declare-fun k2 () node)
(declare-fun Anon18 () node)
(declare-fun Anon61 () node)
(declare-fun Anon19 () node)
(declare-fun Anon62 () node)
(declare-fun l2 () node)
(declare-fun a () node)
(declare-fun r2 () node)
(declare-fun Anon21 () node)
(declare-fun Anon76 () node)
(declare-fun Anon22 () Int)
(declare-fun resn6 () Int)
(declare-fun rl () node)
(declare-fun resl6 () node)
(declare-fun rr () node)
(declare-fun cm5 () Int)
(declare-fun cn5 () Int)
(declare-fun Anon80 () Int)
(declare-fun bm5 () Int)
(declare-fun bn5 () Int)
(declare-fun Anon79 () Int)
(declare-fun resr6 () node)
(declare-fun am5 () Int)
(declare-fun an5 () Int)
(declare-fun Anon77 () Int)
(declare-fun v9 () node)
(declare-fun k1prm () node)
(declare-fun tmp14_8876 () Int)
(declare-fun resn7_8877 () Int)
(declare-fun tmp15_8878 () Int)
(declare-fun resln3_8879 () Int)
(declare-fun am6 () Int)
(declare-fun an6 () Int)
(declare-fun Anon20 () Int)
(declare-fun bm6 () Int)
(declare-fun bn6 () Int)
(declare-fun Anon23 () Int)
(declare-fun cm6 () Int)
(declare-fun cn6 () Int)
(declare-fun Anon24 () Int)
(declare-fun res () node)
(declare-fun Anon70 () Int)
(declare-fun cn () Int)
(declare-fun cm () Int)
(declare-fun Anon69 () Int)
(declare-fun bn () Int)
(declare-fun bm () Int)
(declare-fun Anon66 () Int)
(declare-fun dn () Int)
(declare-fun dm () Int)
(declare-fun Anon63 () Int)
(declare-fun an () Int)
(declare-fun am () Int)


(assert 
(exists ((Anon84 Int)(resl7 node)(Anon85 Int)(resr7 node)(Anon86 Int)(resll3 node)(Anon87 Int)(reslr3 node)(Anon88 Int)(tmp14 Int)(resn7 Int)(tmp15 Int)(resln3 Int))(and 
;lexvar(= cm6 (+ (+ m12 1) m13))
(= (+ Anon24 n15) (+ 1 n14))
(= resrn3 cn6)
(<= (+ 0 n15) (+ n14 1))
(<= n14 (+ 1 n15))
(= Anon83 Anon80)
(= n15 cn5)
(= m12 cm5)
(= Anon82 Anon79)
(= n14 bn5)
(= m13 bm5)
(= q3 resrr3)
(= p3 resrl3)
(= Anon81 Anon78)
(<= dn (+ cn 1))
(<= cn (+ dn 1))
(<= an (+ bn 1))
(<= bn (+ an 1))
(= k1prm k1)
(= Anon6 Anon64)
(= Anon7 Anon65)
(= l k3)
(= r d)
(= cm5 dm)
(= cn5 dn)
(= Anon8 Anon66)
(= Anon9 Anon67)
(= Anon10 Anon68)
(= ll b)
(= lr c)
(= am5 bm)
(= an5 bn)
(= Anon11 Anon69)
(= bm5 cm)
(= bn5 cn)
(= Anon12 Anon70)
(<= 0 cm)
(<= 0 cn)
(<= 0 Anon70)
(<= Anon70 2)
(<= 0 bm)
(<= 0 bn)
(<= 0 Anon69)
(<= Anon69 2)
(distinct k3 nil)
(<= 0 dm)
(<= 0 dn)
(<= 0 Anon66)
(<= Anon66 2)
(distinct k2 nil)
(= resrn3 (+ 1 tmp13))
;eqmax(= resn6 (+ 1 tmp12))
;eqmax(<= 0 Anon8)
(<= Anon8 2)
(<= 0 Anon11)
(<= Anon11 2)
(<= 0 Anon12)
(<= Anon12 2)
(= right2 k2)
(= Anon18 Anon61)
(= Anon19 Anon62)
(= l2 a)
(= r2 v9)
(= am6 am)
(= an6 an)
(= Anon20 Anon63)
(= Anon21 Anon76)
(= Anon22 resn6)
(= rl resl6)
(= rr resr6)
(= bm6 am5)
(= bn6 an5)
(= Anon23 Anon77)
(<= 0 cm5)
(<= 0 cn5)
(<= 0 Anon80)
(<= Anon80 2)
(<= 0 bm5)
(<= 0 bn5)
(<= 0 Anon79)
(<= Anon79 2)
(distinct resr6 nil)
(<= 0 am5)
(<= 0 an5)
(<= 0 Anon77)
(<= Anon77 2)
(distinct v9 nil)
(<= 0 am)
(<= 0 an)
(<= 0 Anon63)
(<= Anon63 2)
(distinct k1prm nil)
(= resln3 (+ 1 tmp14))
;eqmax(= resn7 (+ 1 tmp15))
;eqmax(<= 0 am6)
(<= 0 an6)
(<= 0 Anon20)
(<= Anon20 2)
(<= 0 bm6)
(<= 0 bn6)
(<= 0 Anon23)
(<= Anon23 2)
(<= 0 cm6)
(<= 0 cn6)
(<= 0 Anon24)
(<= Anon24 2)
(tobool (ssep 
(pto res (sref (ref ele Anon84) (ref height resn7) (ref left resl7) (ref right resr7) ))
(pto resl7 (sref (ref ele Anon85) (ref height resln3) (ref left resll3) (ref right reslr3) ))
(avl resr7 cm6 cn6 Anon86)
(avl resll3 am6 an6 Anon87)
(avl reslr3 bm6 bn6 Anon88)
) )
))
)

(assert (not 
(exists ((flted2 Int)(flted3 Int)(Anon89 Int)(ss2 node)(Anon90 Int)(ss3 node)(Anon91 Int)(h3 Int)(t3 Int)(h4 Int)(t4 NUM)(h5 Int)(t5 NUM))(and 
;eqmax(= h5 (+ t5 1))
;eqmax(= h4 (+ t4 1))
;eqmax(= h3 (+ t3 1))
(= flted2 (+ (+ 1 cm) dm))
(= flted3 (+ (+ 1 am) bm))
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
(tobool (ssep 
(pto res (sref (ref ele Anon89) (ref height h3) (ref left ss2) (ref right ss3) ))
(avl ss2 flted3 h4 Anon90)
(avl ss3 flted2 h5 Anon91)
) )
))
))

(check-sat)