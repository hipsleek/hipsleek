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






































































































































































































































































































































(declare-fun Anon18 () Int)
(declare-fun l () node)
(declare-fun Anon21 () Int)
(declare-fun rr () node)
(declare-fun height10 () node)
(declare-fun Anon22 () node)
(declare-fun v31_6921 () Int)
(declare-fun b5 () Int)
(declare-fun n11 () Int)
(declare-fun m9 () Int)
(declare-fun height7 () node)
(declare-fun Anon19 () node)
(declare-fun v7 () Int)
(declare-fun b4 () Int)
(declare-fun n10 () Int)
(declare-fun m8 () Int)
(declare-fun b () Int)
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun left1 () node)
(declare-fun rl () node)
(declare-fun right1 () node)
(declare-fun r () node)
(declare-fun k1prm () node)
(declare-fun k1 () node)
(declare-fun res () node)
(declare-fun Anon24 () Int)
(declare-fun cn () Int)
(declare-fun cm () Int)
(declare-fun Anon23 () Int)
(declare-fun bn () Int)
(declare-fun bm () Int)
(declare-fun Anon20 () Int)
(declare-fun an () Int)
(declare-fun am () Int)


(assert 
(exists ((v31prm Int))(and 
;lexvar(= res r)
(= height10 Anon22)
(= v31prm (+ 1 n11))
(<= v7 n11)
(<= b5 2)
(<= 0 b5)
(<= 0 n11)
(<= 0 m9)
(<= Anon24 2)
(<= 0 Anon24)
(<= 0 cn)
(<= 0 cm)
(= b5 Anon24)
(= n11 cn)
(= m9 cm)
(= height7 Anon19)
(= v7 (+ 1 n10))
(< n n10)
(<= b4 2)
(<= 0 b4)
(<= 0 n10)
(<= 0 m8)
(<= Anon23 2)
(<= 0 Anon23)
(<= 0 bn)
(<= 0 bm)
(= b4 Anon23)
(= n10 bn)
(= m8 bm)
(<= b 2)
(<= 0 b)
(<= 0 n)
(<= 0 m)
(<= Anon20 2)
(<= 0 Anon20)
(<= 0 an)
(<= 0 am)
(= b Anon20)
(= n an)
(= m am)
(= left1 rl)
(= right1 r)
(= k1prm k1)
(tobool (ssep 
(avl l m n b)
(avl rl m8 n10 b4)
(pto k1prm (sref (ref ele Anon18) (ref height v7) (ref left l) (ref right rl) ))
(avl rr m9 n11 b5)
(pto r (sref (ref ele Anon21) (ref height v31prm) (ref left k1prm) (ref right rr) ))
) )
))
)

(assert (not 
(exists ((cm2 Int)(cn2 Int)(am2 Int)(an2 Int)(bm2 Int)(bn2 Int)(Anon25 Int)(resl1 node)(Anon26 Int)(resr1 node)(Anon27 Int)(resll node)(Anon28 Int)(reslr node)(Anon29 Int)(tmp2 Int)(resn1 Int)(tmp3 Int)(resln Int))(and 
(= bn2 bn)
(= bm2 bm)
(= an2 an)
(= am2 am)
(= cn2 cn)
(= cm2 cm)
;eqmax(= resn1 (+ 1 tmp3))
;eqmax(= resln (+ 1 tmp2))
(<= Anon24 2)
(<= 0 Anon24)
(<= 0 cn)
(<= 0 cm)
(<= Anon23 2)
(<= 0 Anon23)
(<= 0 bn)
(<= 0 bm)
(<= Anon20 2)
(<= 0 Anon20)
(<= 0 an)
(<= 0 am)
(tobool (ssep 
(pto res (sref (ref ele Anon25) (ref height resn1) (ref left resl1) (ref right resr1) ))
(pto resl1 (sref (ref ele Anon26) (ref height resln) (ref left resll) (ref right reslr) ))
(avl resr1 cm2 cn2 Anon27)
(avl resll am2 an2 Anon28)
(avl reslr bm2 bn2 Anon29)
) )
))
))

(check-sat)