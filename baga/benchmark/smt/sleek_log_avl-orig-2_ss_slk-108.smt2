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
(declare-fun k1 () node)
(declare-fun Anon33 () Int)
(declare-fun Anon34 () Int)
(declare-fun a () node)
(declare-fun am () Int)
(declare-fun Anon35 () Int)
(declare-fun k2 () node)
(declare-fun Anon36 () Int)
(declare-fun Anon37 () Int)
(declare-fun b () node)
(declare-fun bm () Int)
(declare-fun Anon38 () Int)
(declare-fun c () node)
(declare-fun cm () Int)
(declare-fun Anon39 () Int)
(declare-fun k3prm () node)
(declare-fun k3 () node)
(declare-fun an () Int)
(declare-fun bn () Int)
(declare-fun dn () Int)
(declare-fun cn () Int)


(assert 
(and 
;lexvar(= k3prm k3)
(<= bn (+ an 1))
(<= an (+ bn 1))
(<= cn (+ dn 1))
(<= dn (+ cn 1))
(tobool (ssep 
(pto k3 (sref (ref ele Anon30) (ref height Anon31) (ref left k1) (ref right d) ))
(avl d dm dn Anon32)
(pto k1 (sref (ref ele Anon33) (ref height Anon34) (ref left a) (ref right k2) ))
(avl a am an Anon35)
(pto k2 (sref (ref ele Anon36) (ref height Anon37) (ref left b) (ref right c) ))
(avl b bm bn Anon38)
(avl c cm cn Anon39)
) )
)
)

(assert (not 
(and 
(tobool  
(pto k3prm (sref (ref ele ele21prm) (ref height height21prm) (ref left left21prm) (ref right right21prm) ))
 )
)
))

(check-sat)