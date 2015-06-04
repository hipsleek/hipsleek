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






































































































































































































































































































































(declare-fun Anon6 () Int)
(declare-fun r () node)
(declare-fun Anon9 () Int)
(declare-fun ll () node)
(declare-fun height4 () node)
(declare-fun Anon10 () node)
(declare-fun v17_3487 () Int)
(declare-fun b3 () Int)
(declare-fun n9 () Int)
(declare-fun m7 () Int)
(declare-fun height1 () node)
(declare-fun Anon7 () node)
(declare-fun v3 () Int)
(declare-fun b2 () Int)
(declare-fun n8 () Int)
(declare-fun m6 () Int)
(declare-fun b () Int)
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun right () node)
(declare-fun lr () node)
(declare-fun left () node)
(declare-fun l () node)
(declare-fun k2prm () node)
(declare-fun k2 () node)
(declare-fun res () node)
(declare-fun Anon12 () Int)
(declare-fun bn () Int)
(declare-fun bm () Int)
(declare-fun Anon11 () Int)
(declare-fun an () Int)
(declare-fun am () Int)
(declare-fun Anon8 () Int)
(declare-fun cn () Int)
(declare-fun cm () Int)


(assert 
(exists ((v17prm Int))(and 
;lexvar(= res l)
(= height4 Anon10)
(= v17prm (+ 1 n9))
(<= v3 n9)
(<= b3 2)
(<= 0 b3)
(<= 0 n9)
(<= 0 m7)
(<= Anon11 2)
(<= 0 Anon11)
(<= 0 an)
(<= 0 am)
(= b3 Anon11)
(= n9 an)
(= m7 am)
(= height1 Anon7)
(= v3 (+ 1 n8))
(< n n8)
(<= b2 2)
(<= 0 b2)
(<= 0 n8)
(<= 0 m6)
(<= Anon8 2)
(<= 0 Anon8)
(<= 0 cn)
(<= 0 cm)
(= b2 Anon8)
(= n8 cn)
(= m6 cm)
(<= b 2)
(<= 0 b)
(<= 0 n)
(<= 0 m)
(<= Anon12 2)
(<= 0 Anon12)
(<= 0 bn)
(<= 0 bm)
(= b Anon12)
(= n bn)
(= m bm)
(= right lr)
(= left l)
(= k2prm k2)
(tobool (ssep 
(avl lr m n b)
(avl r m6 n8 b2)
(pto k2prm (sref (ref ele Anon6) (ref height v3) (ref left lr) (ref right r) ))
(avl ll m7 n9 b3)
(pto l (sref (ref ele Anon9) (ref height v17prm) (ref left ll) (ref right k2prm) ))
) )
))
)

(assert (not 
(exists ((am1 Int)(an1 Int)(bm1 Int)(bn1 Int)(cm1 Int)(cn1 Int)(Anon13 Int)(resl node)(Anon14 Int)(resr node)(Anon15 Int)(resrl node)(Anon16 Int)(resrr node)(Anon17 Int)(tmp Int)(resn Int)(tmp1 Int)(resrn Int))(and 
(= cn1 cn)
(= cm1 cm)
(= bn1 bn)
(= bm1 bm)
(= an1 an)
(= am1 am)
;eqmax(= resn (+ 1 tmp1))
;eqmax(= resrn (+ 1 tmp))
(<= Anon12 2)
(<= 0 Anon12)
(<= 0 bn)
(<= 0 bm)
(<= Anon11 2)
(<= 0 Anon11)
(<= 0 an)
(<= 0 am)
(<= Anon8 2)
(<= 0 Anon8)
(<= 0 cn)
(<= 0 cm)
(tobool (ssep 
(pto res (sref (ref ele Anon13) (ref height resn) (ref left resl) (ref right resr) ))
(avl resl am1 an1 Anon14)
(pto resr (sref (ref ele Anon15) (ref height resrn) (ref left resrl) (ref right resrr) ))
(avl resrl bm1 bn1 Anon16)
(avl resrr cm1 cn1 Anon17)
) )
))
))

(check-sat)