(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


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






































































































































































































































































































































(declare-fun p5 () node)
(declare-fun v17 () node)
(declare-fun height21 () Int)
(declare-fun v76_43377 () Int)
(declare-fun b19 () Int)
(declare-fun n49 () Int)
(declare-fun m39 () Int)
(declare-fun b18 () Int)
(declare-fun n46 () Int)
(declare-fun m36 () Int)
(declare-fun b14 () Int)
(declare-fun Anon95 () Int)
(declare-fun n34 () Int)
(declare-fun m27 () Int)
(declare-fun b13 () Int)
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun right4 () node)
(declare-fun q5 () node)
(declare-fun flted17 () Int)
(declare-fun flted18 () Int)
(declare-fun flted19 () Int)
(declare-fun b12 () Int)
(declare-fun Anon96 () Int)
(declare-fun tn2 () Int)
(declare-fun tm2 () Int)
(declare-fun x () Int)
(declare-fun tprm () node)
(declare-fun n21 () Int)
(declare-fun n20 () Int)
(declare-fun n19 () Int)
(declare-fun m17 () Int)
(declare-fun m16 () Int)
(declare-fun Anon97 () Int)
(declare-fun xprm () Int)
(declare-fun v25 () Int)
(declare-fun res () node)
(declare-fun t6 () node)
(declare-fun b () Int)
(declare-fun tn () Int)
(declare-fun tm () Int)


(assert 
(exists ((v76prm Int))(and 
;lexvar(= res tprm)
(= height21 n21)
(= v76prm (+ 1 n46))
(<= n49 n46)
(<= b19 2)
(<= 0 b19)
(<= 0 n49)
(<= 0 m39)
(<= b13 2)
(<= 0 b13)
(<= 0 n)
(<= 0 m)
(= b19 b13)
(= n49 n)
(= m39 m)
(<= b18 2)
(<= 0 b18)
(<= 0 n46)
(<= 0 m36)
(<= b14 2)
(<= 0 b14)
(<= 0 n34)
(<= 0 m27)
(= b18 b14)
(= n46 n34)
(= m36 m27)
(= (+ v25 n34) n)
(<= Anon95 2)
(<= 0 Anon95)
(<= 0 n20)
(<= 0 m17)
(= b14 Anon95)
(= n34 n20)
(= m27 m17)
(<= flted17 2)
(<= 0 flted17)
(<= 0 flted18)
(<= 0 flted19)
(= b13 flted17)
(= n flted18)
(= m flted19)
(= right4 q5)
(<= b12 2)
(<= 0 b12)
(<= 0 tn2)
(<= 0 tm2)
(= q5 nil)
(= tm2 0)
(= tn2 0)
(= flted17 1)
(= flted18 1)
(= flted19 1)
(<= Anon96 2)
(<= 0 Anon96)
(<= 0 n19)
(<= 0 m16)
(= b12 Anon96)
(= tn2 n19)
(= tm2 m16)
(= tprm t6)
(= xprm x)
(distinct tprm nil)
(= n21 tn)
(= (+ b n19) (+ 1 n20))
(<= n20 (+ 1 n19))
(<= (+ 0 n19) (+ n20 1))
(= tm (+ (+ m16 1) m17))
(<= Anon97 xprm)
(distinct v25 2)
(tobool (ssep 
(avl p5 m36 n46 b18)
(avl v17 m39 n49 b19)
(pto tprm (sref (ref ele Anon97) (ref height v76prm) (ref left p5) (ref right v17) ))
) )
))
)

(assert (not 
(exists ((flted29 Int)(flted30 Int)(flted31 Int))(and 
(= t6 nil)
(= tm 0)
(= tn 0)
(= flted29 1)
(= flted30 1)
(= flted31 1)
(<= b 2)
(<= 0 b)
(<= 0 tn)
(<= 0 tm)
(tobool  
(avl res flted31 flted30 flted29)
 )
))
))

(check-sat)