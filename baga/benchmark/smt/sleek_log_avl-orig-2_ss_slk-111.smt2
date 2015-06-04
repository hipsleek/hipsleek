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






































































































































































































































































































































(declare-fun Anon30 () Int)
(declare-fun Anon31 () Int)
(declare-fun d () node)
(declare-fun dm () Int)
(declare-fun Anon32 () Int)
(declare-fun v32prm () node)
(declare-fun Anon40_7444 () Int)
(declare-fun resl2_7445 () node)
(declare-fun Anon41_7446 () Int)
(declare-fun resr2_7447 () node)
(declare-fun Anon42_7448 () Int)
(declare-fun resll1_7449 () node)
(declare-fun Anon43_7450 () Int)
(declare-fun reslr1_7451 () node)
(declare-fun Anon44_7452 () Int)
(declare-fun resn2_7454 () Int)
(declare-fun tmp5_7455 () Int)
(declare-fun resln1_7456 () Int)
(declare-fun tmp4_7453 () Int)
(declare-fun Anon24 () Int)
(declare-fun Anon39 () Int)
(declare-fun cn3 () Int)
(declare-fun cm3 () Int)
(declare-fun cm () Int)
(declare-fun Anon23 () Int)
(declare-fun Anon38 () Int)
(declare-fun bn3 () Int)
(declare-fun bm3 () Int)
(declare-fun bm () Int)
(declare-fun rr () node)
(declare-fun c () node)
(declare-fun rl () node)
(declare-fun b () node)
(declare-fun Anon22 () node)
(declare-fun Anon37 () node)
(declare-fun Anon21 () node)
(declare-fun Anon36 () node)
(declare-fun Anon20 () Int)
(declare-fun Anon35 () Int)
(declare-fun an3 () Int)
(declare-fun am3 () Int)
(declare-fun am () Int)
(declare-fun r () node)
(declare-fun k2 () node)
(declare-fun l () node)
(declare-fun a () node)
(declare-fun Anon19 () node)
(declare-fun Anon34 () node)
(declare-fun Anon18 () node)
(declare-fun Anon33 () node)
(declare-fun t2prm () node)
(declare-fun k1 () node)
(declare-fun k3prm () node)
(declare-fun k3 () node)
(declare-fun an () Int)
(declare-fun bn () Int)
(declare-fun dn () Int)
(declare-fun cn () Int)


(assert 
(exists ((Anon40 Int)(resl2 node)(Anon41 Int)(resr2 node)(Anon42 Int)(resll1 node)(Anon43 Int)(reslr1 node)(Anon44 Int)(tmp4 Int)(resn2 Int)(tmp5 Int)(resln1 Int))(and 
;lexvar(<= Anon24 2)
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
;eqmax(= resn2 (+ 1 tmp5))
;eqmax(= resln1 (+ 1 tmp4))
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
(tobool (ssep 
(pto k3 (sref (ref ele Anon30) (ref height Anon31) (ref left k1) (ref right d) ))
(avl d dm dn Anon32)
(pto v32prm (sref (ref ele Anon40) (ref height resn2) (ref left resl2) (ref right resr2) ))
(pto resl2 (sref (ref ele Anon41) (ref height resln1) (ref left resll1) (ref right reslr1) ))
(avl resr2 cm3 cn3 Anon42)
(avl resll1 am3 an3 Anon43)
(avl reslr1 bm3 bn3 Anon44)
) )
))
)

(assert (not 
(and 
(tobool  
(pto k3prm (sref (ref ele ele22prm) (ref height height22prm) (ref left left22prm) (ref right right22prm) ))
 )
)
))

(check-sat)