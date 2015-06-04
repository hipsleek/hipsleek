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
(declare-fun Anon20 () Int)
(declare-fun bm () Int)
(declare-fun bn () Int)
(declare-fun Anon23 () Int)
(declare-fun cm () Int)
(declare-fun cn () Int)
(declare-fun Anon24 () Int)
(declare-fun Anon18 () Int)
(declare-fun Anon19 () Int)
(declare-fun Anon21 () Int)
(declare-fun Anon22 () Int)
(declare-fun rr () node)
(declare-fun v19prm () node)
(declare-fun l () node)
(declare-fun left1 () node)
(declare-fun rl () node)
(declare-fun right1 () node)
(declare-fun k2prm () node)
(declare-fun r () node)
(declare-fun k1prm () node)
(declare-fun k1 () node)


(assert 
(and 
;lexvar(= v19prm l)
(= left1 rl)
(= right1 r)
(= k2prm r)
(= k1prm k1)
(tobool (ssep 
(avl l am an Anon20)
(avl rl bm bn Anon23)
(avl rr cm cn Anon24)
(pto k1prm (sref (ref ele Anon18) (ref height Anon19) (ref left l) (ref right rl) ))
(pto k2prm (sref (ref ele Anon21) (ref height Anon22) (ref left k1prm) (ref right rr) ))
) )
)
)

(assert (not 
(and 
(tobool  
(avl v19prm m n b)
 )
)
))

(check-sat)