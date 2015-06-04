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






































































































































































































































































































































(declare-fun Anon98_11726 () Int)
(declare-fun p6_11727 () node)
(declare-fun Anon99_11730 () Int)
(declare-fun q6_11731 () node)
(declare-fun Anon100_11734 () Int)
(declare-fun q5 () node)
(declare-fun v47prm () node)
(declare-fun v12 () node)
(declare-fun b8 () Int)
(declare-fun Anon96 () Int)
(declare-fun n22 () Int)
(declare-fun m18 () Int)
(declare-fun left3 () node)
(declare-fun resn9 () Int)
(declare-fun resb1 () Int)
(declare-fun p5 () node)
(declare-fun flted8 () Int)
(declare-fun b6 () Int)
(declare-fun Anon95 () Int)
(declare-fun tn1 () Int)
(declare-fun tm1 () Int)
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
(declare-fun xprm () Int)
(declare-fun Anon97 () Int)
(declare-fun n23_11725 () Int)
(declare-fun b7 () Int)
(declare-fun n () Int)
(declare-fun n24_11729 () Int)
(declare-fun n25_11733 () Int)
(declare-fun m () Int)
(declare-fun m19_11728 () Int)
(declare-fun m20_11732 () Int)


(assert 
(exists ((n23 Int)(Anon98 Int)(p6 node)(m19 Int)(n24 Int)(Anon99 Int)(q6 node)(m20 Int)(n25 Int)(Anon100 Int))(and 
;lexvar(= v47prm v12)
(= (+ 2 n22) n)
(<= b8 2)
(<= 0 b8)
(<= 0 n22)
(<= 0 m18)
(<= Anon96 2)
(<= 0 Anon96)
(<= 0 n19)
(<= 0 m16)
(= b8 Anon96)
(= n22 n19)
(= m18 m16)
(<= b7 2)
(<= 0 b7)
(<= 0 n)
(<= 0 m)
(<= resb1 2)
(<= 0 resb1)
(<= 0 resn9)
(<= 0 flted8)
(= b7 resb1)
(= n resn9)
(= m flted8)
(= left3 p5)
(<= b6 2)
(<= 0 b6)
(<= 0 tn1)
(<= 0 tm1)
(< 0 tn1)
(< 0 tm1)
(distinct p5 nil)
(= flted8 (+ 1 tm1))
(<= Anon95 2)
(<= 0 Anon95)
(<= 0 n20)
(<= 0 m17)
(= b6 Anon95)
(= tn1 n20)
(= tm1 m17)
(= tprm t6)
(= xprm x)
(= tmpprm nil)
(distinct tprm nil)
(= n21 tn)
(= (+ b n19) (+ 1 n20))
(<= n20 (+ 1 n19))
(<= (+ 0 n19) (+ n20 1))
(= tm (+ (+ m16 1) m17))
(< xprm Anon97)
(= n23 n)
(= (+ b7 n25) (+ 1 n24))
(<= n24 (+ 1 n25))
(<= (+ 0 n25) (+ n24 1))
(= m (+ (+ m20 1) m19))
(tobool (ssep 
(pto tprm (sref (ref ele Anon97) (ref height n21) (ref left v12) (ref right q5) ))
(pto v47prm (sref (ref ele Anon98) (ref height n23) (ref left p6) (ref right q6) ))
(avl p6 m19 n24 Anon99)
(avl q6 m20 n25 Anon100)
(avl q5 m18 n22 b8)
) )
))
)

(assert (not 
(and 
(tobool  
(pto v47prm (sref (ref ele ele31prm) (ref height height31prm) (ref left left31prm) (ref right right31prm) ))
 )
)
))

(check-sat)