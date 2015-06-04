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






































































































































































































































































































































(declare-fun am () Int)
(declare-fun Anon63 () Int)
(declare-fun Anon76 () Int)
(declare-fun resl6 () node)
(declare-fun Anon77 () Int)
(declare-fun resr6 () node)
(declare-fun Anon78 () Int)
(declare-fun resrl3 () node)
(declare-fun Anon79 () Int)
(declare-fun resrr3 () node)
(declare-fun Anon80 () Int)
(declare-fun Anon61 () Int)
(declare-fun Anon62 () Int)
(declare-fun a () node)
(declare-fun v34_8560 () node)
(declare-fun right2 () node)
(declare-fun resn6 () Int)
(declare-fun tmp12 () Int)
(declare-fun resrn3 () Int)
(declare-fun tmp13 () Int)
(declare-fun k2 () node)
(declare-fun Anon12 () Int)
(declare-fun Anon70 () Int)
(declare-fun bn5 () Int)
(declare-fun bm5 () Int)
(declare-fun cm () Int)
(declare-fun Anon11 () Int)
(declare-fun Anon69 () Int)
(declare-fun an5 () Int)
(declare-fun am5 () Int)
(declare-fun bm () Int)
(declare-fun lr () node)
(declare-fun c () node)
(declare-fun ll () node)
(declare-fun b () node)
(declare-fun Anon10 () node)
(declare-fun Anon68 () node)
(declare-fun Anon9 () node)
(declare-fun Anon67 () node)
(declare-fun Anon8 () Int)
(declare-fun Anon66 () Int)
(declare-fun cn5 () Int)
(declare-fun cm5 () Int)
(declare-fun dm () Int)
(declare-fun r () node)
(declare-fun d () node)
(declare-fun l () node)
(declare-fun k3 () node)
(declare-fun Anon7 () node)
(declare-fun Anon65 () node)
(declare-fun Anon6 () node)
(declare-fun Anon64 () node)
(declare-fun k1prm () node)
(declare-fun k1 () node)
(declare-fun an () Int)
(declare-fun bn () Int)
(declare-fun dn () Int)
(declare-fun cn () Int)


(assert 
(exists ((v34prm node))(and 
;lexvar(= right2 k2)
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
(tobool (ssep 
(avl a am an Anon63)
(pto v34prm (sref (ref ele Anon76) (ref height resn6) (ref left resl6) (ref right resr6) ))
(avl resl6 am5 an5 Anon77)
(pto resr6 (sref (ref ele Anon78) (ref height resrn3) (ref left resrl3) (ref right resrr3) ))
(avl resrl3 bm5 bn5 Anon79)
(avl resrr3 cm5 cn5 Anon80)
(pto k1prm (sref (ref ele Anon61) (ref height Anon62) (ref left a) (ref right v34prm) ))
) )
))
)

(assert (not 
(and 
(tobool (ssep 
(pto k1prm (sref (ref ele Anon18) (ref height Anon19) (ref left l2) (ref right r2) ))
(avl l2 am6 an6 Anon20)
(pto r2 (sref (ref ele Anon21) (ref height Anon22) (ref left rl) (ref right rr) ))
(avl rl bm6 bn6 Anon23)
(avl rr cm6 cn6 Anon24)
) )
)
))

(check-sat)