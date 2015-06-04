(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun height () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun avl ((?in node) (?m Int) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?m 0)
(= ?n 0)

)(exists ((?n_33 Int))(and 
(= ?m (+ (+ ?m2 1) ?m1))
(<= (+ 0 ?n2) (+ ?n1 1))
(<= ?n1 (+ 1 ?n2))
(= ?n_33 ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref height ?n_33) (ref left ?p) (ref right ?q) ))
(avl ?p ?m1 ?n1)
(avl ?q ?m2 ?n2)
) )
)))))











































































































































































(declare-fun Anon6_427 () Int)
(declare-fun p2_428 () node)
(declare-fun q2_431 () node)
(declare-fun mz () Int)
(declare-fun Anon2 () Int)
(declare-fun Anon3 () Int)
(declare-fun right () node)
(declare-fun Anon5 () node)
(declare-fun left () node)
(declare-fun Anon4 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun yprm () node)
(declare-fun zprm () node)
(declare-fun z () node)
(declare-fun y () node)
(declare-fun ny2 () Int)
(declare-fun n7_426 () Int)
(declare-fun ny () Int)
(declare-fun n9_433 () Int)
(declare-fun n8_430 () Int)
(declare-fun my () Int)
(declare-fun m5_429 () Int)
(declare-fun m6_432 () Int)


(assert 
(exists ((n7 Int)(Anon6 Int)(p2 node)(m5 Int)(n8 Int)(q2 node)(m6 Int)(n9 Int))(and 
;lexvar(= right Anon5)
(= left Anon4)
(= xprm x)
(= yprm y)
(= zprm z)
(distinct y nil)
(= ny2 ny)
(= n7 ny)
(<= n8 (+ 1 n9))
(<= (+ 0 n9) (+ n8 1))
(= my (+ (+ m6 1) m5))
(tobool (ssep 
(pto yprm (sref (ref val Anon6) (ref height n7) (ref left p2) (ref right q2) ))
(avl p2 m5 n8)
(avl q2 m6 n9)
(avl z mz ny2)
(pto xprm (sref (ref val Anon2) (ref height Anon3) (ref left yprm) (ref right zprm) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto yprm (sref (ref val val3prm) (ref height height3prm) (ref left left3prm) (ref right right3prm) ))
 )
)
))

(check-sat)