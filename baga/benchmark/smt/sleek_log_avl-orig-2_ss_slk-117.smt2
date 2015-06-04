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
(declare-fun Anon12 () node)
(declare-fun Anon70 () node)
(declare-fun bn5 () Int)
(declare-fun bm5 () node)
(declare-fun cm () node)
(declare-fun Anon11 () node)
(declare-fun Anon69 () node)
(declare-fun an5 () Int)
(declare-fun am5 () node)
(declare-fun bm () node)
(declare-fun lr () node)
(declare-fun c () node)
(declare-fun ll () node)
(declare-fun b () node)
(declare-fun Anon10 () node)
(declare-fun Anon68 () node)
(declare-fun Anon9 () node)
(declare-fun Anon67 () node)
(declare-fun Anon8 () node)
(declare-fun Anon66 () node)
(declare-fun cn5 () Int)
(declare-fun cm5 () node)
(declare-fun dm () node)
(declare-fun r () node)
(declare-fun d () node)
(declare-fun l () node)
(declare-fun k3 () node)
(declare-fun Anon7 () node)
(declare-fun Anon65 () node)
(declare-fun Anon6 () node)
(declare-fun Anon64 () node)
(declare-fun v33prm () node)
(declare-fun k2 () node)
(declare-fun k1prm () node)
(declare-fun k1 () node)
(declare-fun an () Int)
(declare-fun bn () Int)
(declare-fun dn () Int)
(declare-fun cn () Int)


(assert 
(and 
;lexvar(= Anon12 Anon70)
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
(= v33prm k2)
(= k1prm k1)
(<= bn (+ an 1))
(<= an (+ bn 1))
(<= cn (+ dn 1))
(<= dn (+ cn 1))
(tobool (ssep 
(pto k1 (sref (ref ele Anon61) (ref height Anon62) (ref left a) (ref right k2) ))
(avl a am an Anon63)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)