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






































































































































































































































































































































(declare-fun Anon24 () Int)
(declare-fun cn () Int)
(declare-fun cm () Int)
(declare-fun Anon23 () Int)
(declare-fun bn () Int)
(declare-fun bm () Int)
(declare-fun rr () __Exc)
(declare-fun q10 () __Exc)
(declare-fun rl () __Exc)
(declare-fun p10 () __Exc)
(declare-fun Anon22 () Int)
(declare-fun Anon21 () __Exc)
(declare-fun Anon110 () __Exc)
(declare-fun Anon20 () Int)
(declare-fun an () Int)
(declare-fun am () Int)
(declare-fun r () __Exc)
(declare-fun v16 () __Exc)
(declare-fun l () __Exc)
(declare-fun p5 () __Exc)
(declare-fun Anon19 () Int)
(declare-fun Anon18 () NUM)
(declare-fun b16 () Int)
(declare-fun Anon111 () Int)
(declare-fun m33 () Int)
(declare-fun b15 () Int)
(declare-fun Anon112 () Int)
(declare-fun m32 () Int)
(declare-fun b14 () Int)
(declare-fun Anon95 () Int)
(declare-fun n34 () Int)
(declare-fun m27 () Int)
(declare-fun right3 () __Exc)
(declare-fun resn11 () Int)
(declare-fun resb3 () Int)
(declare-fun q5 () __Exc)
(declare-fun flted16 () Int)
(declare-fun b12 () Int)
(declare-fun Anon96 () Int)
(declare-fun tn2 () Int)
(declare-fun tm2 () Int)
(declare-fun t6 () __Exc)
(declare-fun x () NUM)
(declare-fun tmpprm () __Exc)
(declare-fun tprm () __Exc)
(declare-fun n21 () Int)
(declare-fun b () Int)
(declare-fun tn () Int)
(declare-fun n20 () Int)
(declare-fun n19 () Int)
(declare-fun tm () Int)
(declare-fun m17 () Int)
(declare-fun m16 () Int)
(declare-fun Anon97 () NUM)
(declare-fun xprm () NUM)
(declare-fun n38 () Int)
(declare-fun b13 () Int)
(declare-fun n () Int)
(declare-fun n39 () Int)
(declare-fun n40 () Int)
(declare-fun m () Int)
(declare-fun m31 () Int)
(declare-fun m30 () Int)
(declare-fun n42 () Int)
(declare-fun n41 () Int)


(assert 
(and 
;lexvar(= Anon24 b15)
(= cn n41)
(= cm m32)
(= Anon23 b16)
(= bn n42)
(= bm m33)
(= rr q10)
(= rl p10)
(= Anon22 n38)
(= Anon21 Anon110)
(= Anon20 b14)
(= an n34)
(= am m27)
(= r v16)
(= l p5)
(= Anon19 n21)
(= Anon18 Anon97)
(<= b16 2)
(<= 0 b16)
(<= 0 n42)
(<= 0 m33)
(<= Anon111 2)
(<= 0 Anon111)
(<= 0 n39)
(<= 0 m31)
(= b16 Anon111)
(= n42 n39)
(= m33 m31)
(<= b15 2)
(<= 0 b15)
(<= 0 n41)
(<= 0 m32)
(<= Anon112 2)
(<= 0 Anon112)
(<= 0 n40)
(<= 0 m30)
(= b15 Anon112)
(= n41 n40)
(= m32 m30)
(= (+ 2 n34) n)
(<= b14 2)
(<= 0 b14)
(<= 0 n34)
(<= 0 m27)
(<= Anon95 2)
(<= 0 Anon95)
(<= 0 n20)
(<= 0 m17)
(= b14 Anon95)
(= n34 n20)
(= m27 m17)
(<= b13 2)
(<= 0 b13)
(<= 0 n)
(<= 0 m)
(<= resb3 2)
(<= 0 resb3)
(<= 0 resn11)
(<= 0 flted16)
(= b13 resb3)
(= n resn11)
(= m flted16)
(= right3 q5)
(<= b12 2)
(<= 0 b12)
(<= 0 tn2)
(<= 0 tm2)
(< 0 tn2)
(< 0 tm2)
(distinct q5 nil)
(= flted16 (+ 1 tm2))
(<= Anon96 2)
(<= 0 Anon96)
(<= 0 n19)
(<= 0 m16)
(= b12 Anon96)
(= tn2 n19)
(= tm2 m16)
(= tprm t6)
(= xprm x)
(= tmpprm nil)
(distinct tprm nil)
(= n21 tn)
(= (+ b n19) (+ 1 n20))
(<= n20 (+ 1 n19))
(<= (+ 0 n19) (+ n20 1))
(= tm (+ (+ m16 1) m17))
(<= Anon97 xprm)
(= n38 n)
(= (+ b13 n40) (+ 1 n39))
(<= n39 (+ 1 n40))
(<= (+ 0 n40) (+ n39 1))
(= m (+ (+ m30 1) m31))
(< n42 n41)

)
)

(assert (not 
;lexvar
))

(check-sat)