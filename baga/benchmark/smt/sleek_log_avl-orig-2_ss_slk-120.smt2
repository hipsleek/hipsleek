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






































































































































































































































































































































(declare-fun Anon23 () __Exc)
(declare-fun Anon77 () __Exc)
(declare-fun bn6 () Int)
(declare-fun bm6 () Int)
(declare-fun rr () __Exc)
(declare-fun resr6 () __Exc)
(declare-fun rl () __Exc)
(declare-fun resl6 () __Exc)
(declare-fun Anon22 () Int)
(declare-fun Anon21 () __Exc)
(declare-fun Anon76 () __Exc)
(declare-fun Anon20 () __Exc)
(declare-fun Anon63 () __Exc)
(declare-fun an6 () Int)
(declare-fun am6 () __Exc)
(declare-fun am () __Exc)
(declare-fun r2 () __Exc)
(declare-fun v9 () __Exc)
(declare-fun l2 () __Exc)
(declare-fun a () __Exc)
(declare-fun Anon19 () __Exc)
(declare-fun Anon62 () __Exc)
(declare-fun Anon18 () __Exc)
(declare-fun Anon61 () __Exc)
(declare-fun right2 () __Exc)
(declare-fun resn6 () Int)
(declare-fun tmp12 () Int)
(declare-fun tmp13 () Int)
(declare-fun k2 () __Exc)
(declare-fun Anon12 () Int)
(declare-fun Anon70 () Int)
(declare-fun cm () Int)
(declare-fun Anon11 () Int)
(declare-fun Anon69 () Int)
(declare-fun an5 () Int)
(declare-fun am5 () Int)
(declare-fun bm () Int)
(declare-fun lr () __Exc)
(declare-fun c () __Exc)
(declare-fun ll () __Exc)
(declare-fun b () __Exc)
(declare-fun Anon10 () __Exc)
(declare-fun Anon68 () __Exc)
(declare-fun Anon9 () __Exc)
(declare-fun Anon67 () __Exc)
(declare-fun Anon8 () Int)
(declare-fun Anon66 () Int)
(declare-fun dm () Int)
(declare-fun r () __Exc)
(declare-fun d () __Exc)
(declare-fun l () __Exc)
(declare-fun k3 () __Exc)
(declare-fun Anon7 () __Exc)
(declare-fun Anon65 () __Exc)
(declare-fun Anon6 () __Exc)
(declare-fun Anon64 () __Exc)
(declare-fun k1prm () __Exc)
(declare-fun k1 () __Exc)
(declare-fun an () Int)
(declare-fun bn () Int)
(declare-fun dn () Int)
(declare-fun cn () Int)
(declare-fun Anon81 () __Exc)
(declare-fun Anon78 () __Exc)
(declare-fun p3 () __Exc)
(declare-fun resrl3 () __Exc)
(declare-fun q3 () __Exc)
(declare-fun resrr3 () __Exc)
(declare-fun bm5 () Int)
(declare-fun bn5 () Int)
(declare-fun Anon82 () __Exc)
(declare-fun Anon79 () __Exc)
(declare-fun cm5 () Int)
(declare-fun cn5 () Int)
(declare-fun Anon83 () __Exc)
(declare-fun Anon80 () __Exc)
(declare-fun resrn3 () Int)
(declare-fun Anon24 () Int)
(declare-fun cn6 () Int)
(declare-fun n14 () Int)
(declare-fun n15 () Int)
(declare-fun cm6 () Int)
(declare-fun m13 () Int)
(declare-fun m12 () Int)


(assert 
(and 
;lexvar(= Anon23 Anon77)
(= bn6 an5)
(= bm6 am5)
(= rr resr6)
(= rl resl6)
(= Anon22 resn6)
(= Anon21 Anon76)
(= Anon20 Anon63)
(= an6 an)
(= am6 am)
(= r2 v9)
(= l2 a)
(= Anon19 Anon62)
(= Anon18 Anon61)
(= right2 k2)
(<= Anon12 2)
(<= 0 Anon12)
(<= 0 bn5)
(<= 0 bm5)
(<= Anon11 2)
(<= 0 Anon11)
(<= 0 an5)
(<= 0 am5)
(<= Anon8 2)
(<= 0 Anon8)
(<= 0 cn5)
(<= 0 cm5)
;eqmax(= resn6 (+ 1 tmp12))
;eqmax(= resrn3 (+ 1 tmp13))
(distinct k2 nil)
(<= Anon66 2)
(<= 0 Anon66)
(<= 0 dn)
(<= 0 dm)
(distinct k3 nil)
(<= Anon69 2)
(<= 0 Anon69)
(<= 0 bn)
(<= 0 bm)
(<= Anon70 2)
(<= 0 Anon70)
(<= 0 cn)
(<= 0 cm)
(= Anon12 Anon70)
(= bn5 cn)
(= bm5 cm)
(= Anon11 Anon69)
(= an5 bn)
(= am5 bm)
(= lr c)
(= ll b)
(= Anon10 Anon68)
(= Anon9 Anon67)
(= Anon8 Anon66)
(= cn5 dn)
(= cm5 dm)
(= r d)
(= l k3)
(= Anon7 Anon65)
(= Anon6 Anon64)
(= k1prm k1)
(<= bn (+ an 1))
(<= an (+ bn 1))
(<= cn (+ dn 1))
(<= dn (+ cn 1))
(= Anon81 Anon78)
(= p3 resrl3)
(= q3 resrr3)
(= m13 bm5)
(= n14 bn5)
(= Anon82 Anon79)
(= m12 cm5)
(= n15 cn5)
(= Anon83 Anon80)
(<= n14 (+ 1 n15))
(<= (+ 0 n15) (+ n14 1))
(= resrn3 cn6)
(= (+ Anon24 n15) (+ 1 n14))
(= cm6 (+ (+ m12 1) m13))

)
)

(assert (not 
;lexvar
))

(check-sat)