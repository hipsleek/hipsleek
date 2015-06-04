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
(declare-fun an () Int)
(declare-fun Anon11 () Int)
(declare-fun Anon6 () Int)
(declare-fun Anon7 () Int)
(declare-fun Anon9 () Int)
(declare-fun Anon10 () Int)
(declare-fun ll () node)
(declare-fun r () node)
(declare-fun v9prm () Int)
(declare-fun v10prm () Int)
(declare-fun b2 () Int)
(declare-fun Anon8 () Int)
(declare-fun n8 () Int)
(declare-fun cn () Int)
(declare-fun m6 () Int)
(declare-fun cm () Int)
(declare-fun b () Int)
(declare-fun Anon12 () Int)
(declare-fun n () Int)
(declare-fun bn () Int)
(declare-fun m () Int)
(declare-fun bm () Int)
(declare-fun right () node)
(declare-fun lr () node)
(declare-fun left () node)
(declare-fun k1prm () node)
(declare-fun l () node)
(declare-fun k2prm () node)
(declare-fun k2 () node)


(assert 
(and 
;lexvar(= v9prm 1)
(< n n8)
(= v10prm n8)
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
(= k1prm l)
(= k2prm k2)
(tobool (ssep 
(avl ll am an Anon11)
(pto k2prm (sref (ref ele Anon6) (ref height Anon7) (ref left lr) (ref right r) ))
(pto k1prm (sref (ref ele Anon9) (ref height Anon10) (ref left ll) (ref right k2prm) ))
(avl lr m n b)
(avl r m6 n8 b2)
) )
)
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)