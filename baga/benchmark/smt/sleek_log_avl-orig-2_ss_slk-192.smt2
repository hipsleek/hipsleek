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






































































































































































































































































































































(declare-fun Anon107_16195 () Int)
(declare-fun p9_16196 () node)
(declare-fun Anon108_16199 () Int)
(declare-fun q9_16200 () node)
(declare-fun Anon109_16203 () Int)
(declare-fun p5 () node)
(declare-fun v63prm () node)
(declare-fun v16 () node)
(declare-fun b14 () Int)
(declare-fun Anon95 () Int)
(declare-fun n34 () Int)
(declare-fun m27 () Int)
(declare-fun right3 () node)
(declare-fun resn11 () Int)
(declare-fun resb3 () Int)
(declare-fun q5 () node)
(declare-fun flted16 () Int)
(declare-fun b12 () Int)
(declare-fun Anon96 () Int)
(declare-fun tn2 () Int)
(declare-fun tm2 () Int)
(declare-fun t6 () node)
(declare-fun x () Int)
(declare-fun tmpprm () node)
(declare-fun tprm () node)
(declare-fun n21 () Int)
(declare-fun b () Int)
(declare-fun tn () Int)
(declare-fun n20 () Int)
(declare-fun n19 () Int)
(declare-fun tm () Int)
(declare-fun m17 () Int)
(declare-fun m16 () Int)
(declare-fun Anon97 () Int)
(declare-fun xprm () Int)
(declare-fun n35_16194 () Int)
(declare-fun b13 () Int)
(declare-fun n () Int)
(declare-fun n36_16198 () Int)
(declare-fun n37_16202 () Int)
(declare-fun m () Int)
(declare-fun m28_16197 () Int)
(declare-fun m29_16201 () Int)


(assert 
(exists ((n35 Int)(Anon107 Int)(p9 node)(m28 Int)(n36 Int)(Anon108 Int)(q9 node)(m29 Int)(n37 Int)(Anon109 Int))(and 
;lexvar(= v63prm v16)
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
(= n35 n)
(= (+ b13 n37) (+ 1 n36))
(<= n36 (+ 1 n37))
(<= (+ 0 n37) (+ n36 1))
(= m (+ (+ m29 1) m28))
(tobool (ssep 
(pto tprm (sref (ref ele Anon97) (ref height n21) (ref left p5) (ref right v16) ))
(pto v63prm (sref (ref ele Anon107) (ref height n35) (ref left p9) (ref right q9) ))
(avl p9 m28 n36 Anon108)
(avl q9 m29 n37 Anon109)
(avl p5 m27 n34 b14)
) )
))
)

(assert (not 
(and 
(tobool  
(pto v63prm (sref (ref ele ele39prm) (ref height height39prm) (ref left left39prm) (ref right right39prm) ))
 )
)
))

(check-sat)