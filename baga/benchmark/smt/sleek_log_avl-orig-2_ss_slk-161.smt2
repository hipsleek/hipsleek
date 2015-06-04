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






































































































































































































































































































































(declare-fun Anon101 () Int)
(declare-fun p7 () node)
(declare-fun q7 () node)
(declare-fun v12 () node)
(declare-fun q5 () node)
(declare-fun n26 () Int)
(declare-fun Anon97 () Int)
(declare-fun tm () Int)
(declare-fun b () Int)
(declare-fun n21 () Int)
(declare-fun tn () Int)
(declare-fun tmpprm () node)
(declare-fun xprm () Int)
(declare-fun x () Int)
(declare-fun tprm () node)
(declare-fun t6 () node)
(declare-fun m17 () Int)
(declare-fun n20 () Int)
(declare-fun Anon95 () Int)
(declare-fun tm1 () Int)
(declare-fun tn1 () Int)
(declare-fun b6 () Int)
(declare-fun left3 () node)
(declare-fun p5 () node)
(declare-fun flted8 () Int)
(declare-fun resn9 () Int)
(declare-fun resb1 () Int)
(declare-fun m () Int)
(declare-fun b7 () Int)
(declare-fun m16 () Int)
(declare-fun n19 () Int)
(declare-fun Anon96 () Int)
(declare-fun m18 () Int)
(declare-fun b8 () Int)
(declare-fun n22 () Int)
(declare-fun n () Int)
(declare-fun m22 () Int)
(declare-fun n27 () Int)
(declare-fun Anon102 () Int)
(declare-fun m23 () Int)
(declare-fun n29 () Int)
(declare-fun b9 () Int)
(declare-fun m21 () Int)
(declare-fun n28 () Int)
(declare-fun Anon103 () Int)
(declare-fun m24 () Int)
(declare-fun n30 () Int)
(declare-fun b10 () Int)
(declare-fun v52prm () Int)
(declare-fun v49prm () Int)


(assert 
(and 
;lexvar(= m (+ (+ m21 1) m22))
(<= (+ 0 n28) (+ n27 1))
(<= n27 (+ 1 n28))
(= (+ b7 n28) (+ 1 n27))
(= n26 n)
(< xprm Anon97)
(= tm (+ (+ m16 1) m17))
(<= (+ 0 n19) (+ n20 1))
(<= n20 (+ 1 n19))
(= (+ b n19) (+ 1 n20))
(= n21 tn)
(distinct tprm nil)
(= tmpprm nil)
(= xprm x)
(= tprm t6)
(= tm1 m17)
(= tn1 n20)
(= b6 Anon95)
(<= 0 m17)
(<= 0 n20)
(<= 0 Anon95)
(<= Anon95 2)
(= flted8 (+ 1 tm1))
(distinct p5 nil)
(< 0 tm1)
(< 0 tn1)
(<= 0 tm1)
(<= 0 tn1)
(<= 0 b6)
(<= b6 2)
(= left3 p5)
(= m flted8)
(= n resn9)
(= b7 resb1)
(<= 0 flted8)
(<= 0 resn9)
(<= 0 resb1)
(<= resb1 2)
(<= 0 m)
(<= 0 n)
(<= 0 b7)
(<= b7 2)
(= m18 m16)
(= n22 n19)
(= b8 Anon96)
(<= 0 m16)
(<= 0 n19)
(<= 0 Anon96)
(<= Anon96 2)
(<= 0 m18)
(<= 0 n22)
(<= 0 b8)
(<= b8 2)
(= (+ 2 n22) n)
(= m23 m22)
(= n29 n27)
(= b9 Anon102)
(<= 0 m22)
(<= 0 n27)
(<= 0 Anon102)
(<= Anon102 2)
(= v49prm n29)
(<= 0 m23)
(<= 0 n29)
(<= 0 b9)
(<= b9 2)
(= m24 m21)
(= n30 n28)
(= b10 Anon103)
(<= 0 m21)
(<= 0 n28)
(<= 0 Anon103)
(<= Anon103 2)
(= v52prm n30)
(<= 0 m24)
(<= 0 n30)
(<= 0 b10)
(<= b10 2)
(< v52prm v49prm)
(tobool (ssep 
(pto v12 (sref (ref ele Anon101) (ref height n26) (ref left p7) (ref right q7) ))
(avl p7 m23 n29 b9)
(avl q7 m24 n30 b10)
(pto tprm (sref (ref ele Anon97) (ref height n21) (ref left v12) (ref right q5) ))
(avl q5 m18 n22 b8)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)