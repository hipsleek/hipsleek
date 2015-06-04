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
(declare-fun Anon7 () Int)
(declare-fun r () node)
(declare-fun cm () Int)
(declare-fun cn () Int)
(declare-fun Anon8 () Int)
(declare-fun l () node)
(declare-fun Anon9 () Int)
(declare-fun Anon10 () Int)
(declare-fun ll () node)
(declare-fun am () Int)
(declare-fun an () Int)
(declare-fun Anon11 () Int)
(declare-fun lr () node)
(declare-fun bm () Int)
(declare-fun bn () Int)
(declare-fun Anon12 () Int)
(declare-fun k2prm () node)
(declare-fun k2 () node)


(assert 
(and 
;lexvar(= k2prm k2)
(tobool (ssep 
(pto k2 (sref (ref ele Anon6) (ref height Anon7) (ref left l) (ref right r) ))
(avl r cm cn Anon8)
(pto l (sref (ref ele Anon9) (ref height Anon10) (ref left ll) (ref right lr) ))
(avl ll am an Anon11)
(avl lr bm bn Anon12)
) )
)
)

(assert (not 
(and 
(tobool  
(pto k2prm (sref (ref ele ele1prm) (ref height height1prm) (ref left left1prm) (ref right right1prm) ))
 )
)
))

(check-sat)