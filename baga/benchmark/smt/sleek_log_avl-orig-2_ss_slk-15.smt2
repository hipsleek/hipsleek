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






































































































































































































































































































































(declare-fun Anon3 () Int)
(declare-fun p1 () node)
(declare-fun Anon4 () Int)
(declare-fun q1 () node)
(declare-fun Anon5 () Int)
(declare-fun v3prm () Int)
(declare-fun xprm () node)
(declare-fun n5 () Int)
(declare-fun n6 () Int)
(declare-fun n7 () Int)
(declare-fun m5 () Int)
(declare-fun m4 () Int)
(declare-fun x () node)
(declare-fun res () Int)
(declare-fun b () Int)
(declare-fun n () Int)
(declare-fun m () Int)


(assert 
(and 
;lexvar(= res v3prm)
(= v3prm n5)
(= xprm x)
(distinct xprm nil)
(= n5 n)
(= (+ b n7) (+ 1 n6))
(<= n6 (+ 1 n7))
(<= (+ 0 n7) (+ n6 1))
(= m (+ (+ m4 1) m5))
(tobool (ssep 
(pto xprm (sref (ref ele Anon3) (ref height n5) (ref left p1) (ref right q1) ))
(avl p1 m5 n6 Anon4)
(avl q1 m4 n7 Anon5)
) )
)
)

(assert (not 
(exists ((m3 Int)(n4 Int)(b1 Int))(and 
(= b1 b)
(= n4 n)
(= m3 m)
(= res n)
(<= b 2)
(<= 0 b)
(<= 0 n)
(<= 0 m)
(tobool  
(avl x m3 n4 b1)
 )
))
))

(check-sat)