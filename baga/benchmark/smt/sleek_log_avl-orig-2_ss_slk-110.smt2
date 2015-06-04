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
(declare-fun Anon24 () node)
(declare-fun Anon39 () node)
(declare-fun cn3 () Int)
(declare-fun cm3 () node)
(declare-fun cm () node)
(declare-fun Anon23 () node)
(declare-fun Anon38 () node)
(declare-fun bn3 () Int)
(declare-fun bm3 () node)
(declare-fun bm () node)
(declare-fun rr () node)
(declare-fun c () node)
(declare-fun rl () node)
(declare-fun b () node)
(declare-fun Anon22 () node)
(declare-fun Anon37 () node)
(declare-fun Anon21 () node)
(declare-fun Anon36 () node)
(declare-fun Anon20 () node)
(declare-fun Anon35 () node)
(declare-fun an3 () Int)
(declare-fun am3 () node)
(declare-fun am () node)
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
(and 
;lexvar(= Anon24 Anon39)
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
) )
)
)

(assert (not 
;lexvar
))

(check-sat)