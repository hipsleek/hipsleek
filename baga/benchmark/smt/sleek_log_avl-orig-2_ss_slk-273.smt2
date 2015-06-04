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






































































































































































































































































































































(declare-fun v12 () node)
(declare-fun q5 () node)
(declare-fun v74prm () Int)
(declare-fun v75prm () Int)
(declare-fun b19 () Int)
(declare-fun n49 () Int)
(declare-fun m39 () Int)
(declare-fun b18 () Int)
(declare-fun n46 () Int)
(declare-fun m36 () Int)
(declare-fun b8 () Int)
(declare-fun Anon96 () Int)
(declare-fun n22 () Int)
(declare-fun m18 () Int)
(declare-fun b7 () Int)
(declare-fun n () Int)
(declare-fun m () Int)
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
(declare-fun v22 () Int)


(assert 
(and 
;lexvar(= v74prm 1)
(<= n49 n46)
(= v75prm n46)
(<= b19 2)
(<= 0 b19)
(<= 0 n49)
(<= 0 m39)
(<= b8 2)
(<= 0 b8)
(<= 0 n22)
(<= 0 m18)
(= b19 b8)
(= n49 n22)
(= m39 m18)
(<= b18 2)
(<= 0 b18)
(<= 0 n46)
(<= 0 m36)
(<= b7 2)
(<= 0 b7)
(<= 0 n)
(<= 0 m)
(= b18 b7)
(= n46 n)
(= m36 m)
(= (+ v22 n22) n)
(<= Anon96 2)
(<= 0 Anon96)
(<= 0 n19)
(<= 0 m16)
(= b8 Anon96)
(= n22 n19)
(= m18 m16)
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
(distinct v22 2)
(tobool (ssep 
(avl v12 m36 n46 b18)
(pto tprm (sref (ref ele Anon97) (ref height n21) (ref left v12) (ref right q5) ))
(avl q5 m39 n49 b19)
) )
)
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)