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






































































































































































































































































































































(declare-fun Anon61 () Int)
(declare-fun Anon62 () Int)
(declare-fun a () node)
(declare-fun am () Int)
(declare-fun Anon63 () Int)
(declare-fun v34prm () node)
(declare-fun Anon71_8434 () Int)
(declare-fun resl5_8435 () node)
(declare-fun Anon72_8436 () Int)
(declare-fun resr5_8437 () node)
(declare-fun Anon73_8438 () Int)
(declare-fun resrl2_8439 () node)
(declare-fun Anon74_8440 () Int)
(declare-fun resrr2_8441 () node)
(declare-fun Anon75_8442 () Int)
(declare-fun resn5_8444 () Int)
(declare-fun tmp11_8445 () Int)
(declare-fun resrn2_8446 () Int)
(declare-fun tmp10_8443 () Int)
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
(exists ((Anon71 Int)(resl5 node)(Anon72 Int)(resr5 node)(Anon73 Int)(resrl2 node)(Anon74 Int)(resrr2 node)(Anon75 Int)(tmp10 Int)(resn5 Int)(tmp11 Int)(resrn2 Int))(and 
;lexvar(<= Anon12 2)
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
;eqmax(= resn5 (+ 1 tmp11))
;eqmax(= resrn2 (+ 1 tmp10))
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
(pto k1 (sref (ref ele Anon61) (ref height Anon62) (ref left a) (ref right k2) ))
(avl a am an Anon63)
(pto v34prm (sref (ref ele Anon71) (ref height resn5) (ref left resl5) (ref right resr5) ))
(avl resl5 am5 an5 Anon72)
(pto resr5 (sref (ref ele Anon73) (ref height resrn2) (ref left resrl2) (ref right resrr2) ))
(avl resrl2 bm5 bn5 Anon74)
(avl resrr2 cm5 cn5 Anon75)
) )
))
)

(assert (not 
(and 
(tobool  
(pto k1prm (sref (ref ele ele24prm) (ref height height24prm) (ref left left24prm) (ref right right24prm) ))
 )
)
))

(check-sat)