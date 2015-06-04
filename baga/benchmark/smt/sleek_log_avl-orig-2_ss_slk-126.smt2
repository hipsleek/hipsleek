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






































































































































































































































































































































(declare-fun Anon92_9329 () Int)
(declare-fun p4_9330 () node)
(declare-fun Anon93_9333 () Int)
(declare-fun q4_9334 () node)
(declare-fun Anon94_9337 () Int)
(declare-fun t6 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun tmpprm () node)
(declare-fun tprm () node)
(declare-fun n16_9328 () Int)
(declare-fun b () Int)
(declare-fun tn () Int)
(declare-fun n17_9332 () Int)
(declare-fun n18_9336 () Int)
(declare-fun tm () Int)
(declare-fun m14_9331 () Int)
(declare-fun m15_9335 () Int)


(assert 
(exists ((n16 Int)(Anon92 Int)(p4 node)(m14 Int)(n17 Int)(Anon93 Int)(q4 node)(m15 Int)(n18 Int)(Anon94 Int))(and 
;lexvar(= tprm t6)
(= xprm x)
(= tmpprm nil)
(distinct tprm nil)
(= n16 tn)
(= (+ b n18) (+ 1 n17))
(<= n17 (+ 1 n18))
(<= (+ 0 n18) (+ n17 1))
(= tm (+ (+ m15 1) m14))
(tobool (ssep 
(pto tprm (sref (ref ele Anon92) (ref height n16) (ref left p4) (ref right q4) ))
(avl p4 m14 n17 Anon93)
(avl q4 m15 n18 Anon94)
) )
))
)

(assert (not 
(and 
(tobool  
(pto tprm (sref (ref ele ele25prm) (ref height height25prm) (ref left left25prm) (ref right right25prm) ))
 )
)
))

(check-sat)