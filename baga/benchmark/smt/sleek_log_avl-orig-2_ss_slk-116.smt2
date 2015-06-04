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
(declare-fun Anon64 () Int)
(declare-fun Anon65 () Int)
(declare-fun d () node)
(declare-fun dm () Int)
(declare-fun Anon66 () Int)
(declare-fun k3 () node)
(declare-fun Anon67 () Int)
(declare-fun Anon68 () Int)
(declare-fun b () node)
(declare-fun bm () Int)
(declare-fun Anon69 () Int)
(declare-fun c () node)
(declare-fun cm () Int)
(declare-fun Anon70 () Int)
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
;lexvar(= v33prm k2)
(= k1prm k1)
(<= bn (+ an 1))
(<= an (+ bn 1))
(<= cn (+ dn 1))
(<= dn (+ cn 1))
(tobool (ssep 
(pto k1 (sref (ref ele Anon61) (ref height Anon62) (ref left a) (ref right k2) ))
(avl a am an Anon63)
(pto k2 (sref (ref ele Anon64) (ref height Anon65) (ref left k3) (ref right d) ))
(avl d dm dn Anon66)
(pto k3 (sref (ref ele Anon67) (ref height Anon68) (ref left b) (ref right c) ))
(avl b bm bn Anon69)
(avl c cm cn Anon70)
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(pto v33prm (sref (ref ele Anon6) (ref height Anon7) (ref left l) (ref right r) ))
(pto l (sref (ref ele Anon9) (ref height Anon10) (ref left ll) (ref right lr) ))
(avl r cm5 cn5 Anon8)
(avl ll am5 an5 Anon11)
(avl lr bm5 bn5 Anon12)
) )
)
))

(check-sat)