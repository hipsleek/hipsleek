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






































































































































































































































































































































(declare-fun Anon12 () __Exc)
(declare-fun Anon47 () __Exc)
(declare-fun bn4 () Int)
(declare-fun bm4 () Int)
(declare-fun lr () __Exc)
(declare-fun resr3 () __Exc)
(declare-fun ll () __Exc)
(declare-fun resl3 () __Exc)
(declare-fun Anon10 () Int)
(declare-fun Anon9 () __Exc)
(declare-fun Anon45 () __Exc)
(declare-fun Anon8 () __Exc)
(declare-fun Anon32 () __Exc)
(declare-fun cn4 () Int)
(declare-fun cm4 () __Exc)
(declare-fun dm () __Exc)
(declare-fun r1 () __Exc)
(declare-fun d () __Exc)
(declare-fun l1 () __Exc)
(declare-fun v8 () __Exc)
(declare-fun Anon7 () __Exc)
(declare-fun Anon31 () __Exc)
(declare-fun Anon6 () __Exc)
(declare-fun Anon30 () __Exc)
(declare-fun left2 () __Exc)
(declare-fun resn3 () Int)
(declare-fun tmp6 () Int)
(declare-fun tmp7 () Int)
(declare-fun Anon24 () Int)
(declare-fun Anon39 () Int)
(declare-fun cn3 () Int)
(declare-fun cm3 () Int)
(declare-fun cm () Int)
(declare-fun Anon23 () Int)
(declare-fun Anon38 () Int)
(declare-fun bm () Int)
(declare-fun rr () __Exc)
(declare-fun c () __Exc)
(declare-fun rl () __Exc)
(declare-fun b () __Exc)
(declare-fun Anon22 () __Exc)
(declare-fun Anon37 () __Exc)
(declare-fun Anon21 () __Exc)
(declare-fun Anon36 () __Exc)
(declare-fun Anon20 () Int)
(declare-fun Anon35 () Int)
(declare-fun am () Int)
(declare-fun r () __Exc)
(declare-fun k2 () __Exc)
(declare-fun l () __Exc)
(declare-fun a () __Exc)
(declare-fun Anon19 () __Exc)
(declare-fun Anon34 () __Exc)
(declare-fun Anon18 () __Exc)
(declare-fun Anon33 () __Exc)
(declare-fun t2prm () __Exc)
(declare-fun k1 () __Exc)
(declare-fun k3prm () __Exc)
(declare-fun k3 () __Exc)
(declare-fun an () Int)
(declare-fun bn () Int)
(declare-fun dn () Int)
(declare-fun cn () Int)
(declare-fun Anon50 () __Exc)
(declare-fun Anon46 () __Exc)
(declare-fun p2 () __Exc)
(declare-fun resll2 () __Exc)
(declare-fun q2 () __Exc)
(declare-fun reslr2 () __Exc)
(declare-fun am3 () Int)
(declare-fun an3 () Int)
(declare-fun Anon51 () __Exc)
(declare-fun Anon48 () __Exc)
(declare-fun bm3 () Int)
(declare-fun bn3 () Int)
(declare-fun Anon52 () __Exc)
(declare-fun Anon49 () __Exc)
(declare-fun resln2 () Int)
(declare-fun Anon11 () Int)
(declare-fun an4 () Int)
(declare-fun n12 () Int)
(declare-fun n13 () Int)
(declare-fun am4 () Int)
(declare-fun m11 () Int)
(declare-fun m10 () Int)


(assert 
(and 
;lexvar(= Anon12 Anon47)
(= bn4 cn3)
(= bm4 cm3)
(= lr resr3)
(= ll resl3)
(= Anon10 resn3)
(= Anon9 Anon45)
(= Anon8 Anon32)
(= cn4 dn)
(= cm4 dm)
(= r1 d)
(= l1 v8)
(= Anon7 Anon31)
(= Anon6 Anon30)
(= left2 k1)
(<= Anon24 2)
(<= 0 Anon24)
(<= 0 cn3)
(<= 0 cm3)
(<= Anon23 2)
(<= 0 Anon23)
(<= 0 bn3)
(<= 0 bm3)
(<= Anon20 2)
(<= 0 Anon20)
(<= 0 an3)
(<= 0 am3)
;eqmax(= resn3 (+ 1 tmp6))
;eqmax(= resln2 (+ 1 tmp7))
(distinct k1 nil)
(<= Anon35 2)
(<= 0 Anon35)
(<= 0 an)
(<= 0 am)
(distinct k2 nil)
(<= Anon38 2)
(<= 0 Anon38)
(<= 0 bn)
(<= 0 bm)
(<= Anon39 2)
(<= 0 Anon39)
(<= 0 cn)
(<= 0 cm)
(= Anon24 Anon39)
(= cn3 cn)
(= cm3 cm)
(= Anon23 Anon38)
(= bn3 bn)
(= bm3 bm)
(= rr c)
(= rl b)
(= Anon22 Anon37)
(= Anon21 Anon36)
(= Anon20 Anon35)
(= an3 an)
(= am3 am)
(= r k2)
(= l a)
(= Anon19 Anon34)
(= Anon18 Anon33)
(= t2prm k1)
(= k3prm k3)
(<= bn (+ an 1))
(<= an (+ bn 1))
(<= cn (+ dn 1))
(<= dn (+ cn 1))
(= Anon50 Anon46)
(= p2 resll2)
(= q2 reslr2)
(= m11 am3)
(= n12 an3)
(= Anon51 Anon48)
(= m10 bm3)
(= n13 bn3)
(= Anon52 Anon49)
(<= n12 (+ 1 n13))
(<= (+ 0 n13) (+ n12 1))
(= resln2 an4)
(= (+ Anon11 n13) (+ 1 n12))
(= am4 (+ (+ m10 1) m11))

)
)

(assert (not 
;lexvar
))

(check-sat)