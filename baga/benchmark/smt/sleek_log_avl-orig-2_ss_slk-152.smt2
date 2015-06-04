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






































































































































































































































































































































(declare-fun v13 () node)
(declare-fun q5 () node)
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
(declare-fun left4 () node)
(declare-fun p5 () node)
(declare-fun flted11 () Int)
(declare-fun flted10 () Int)
(declare-fun flted9 () Int)
(declare-fun m () Int)
(declare-fun b7 () Int)
(declare-fun m16 () Int)
(declare-fun n19 () Int)
(declare-fun Anon96 () Int)
(declare-fun m18 () Int)
(declare-fun b8 () Int)
(declare-fun n22 () Int)
(declare-fun n () Int)
(declare-fun v44prm () Int)
(declare-fun v45prm () Int)


(assert 
(and 
;lexvar(< xprm Anon97)
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
(= flted11 1)
(= flted10 1)
(= flted9 1)
(= tn1 0)
(= tm1 0)
(= p5 nil)
(<= 0 tm1)
(<= 0 tn1)
(<= 0 b6)
(<= b6 2)
(= left4 p5)
(= m flted11)
(= n flted10)
(= b7 flted9)
(<= 0 flted11)
(<= 0 flted10)
(<= 0 flted9)
(<= flted9 2)
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
(= (+ v44prm n22) n)
(= v45prm 2)
(distinct v44prm v45prm)
(tobool (ssep 
(avl v13 m n b7)
(pto tprm (sref (ref ele Anon97) (ref height n21) (ref left v13) (ref right q5) ))
(avl q5 m18 n22 b8)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)