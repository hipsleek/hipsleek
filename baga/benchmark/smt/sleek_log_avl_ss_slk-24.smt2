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

(define-fun avl ((?in node) (?size Int) (?height Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?size 0)
(= ?height 0)

)(exists ((?height_34 Int))(and 
(= ?size (+ (+ ?size2 1) ?size1))
(<= ?height2 (+ 1 ?height1))
(<= ?height1 (+ 1 ?height2))
(= ?height_34 ?height)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref height ?height_34) (ref left ?p) (ref right ?q) ))
(avl ?p ?size1 ?height1)
(avl ?q ?size2 ?height2)
) )
)))))























































































































































































































































































































































































































































(declare-fun Anon9 () Int)
(declare-fun p5 () node)
(declare-fun q5 () node)
(declare-fun v9prm () Int)
(declare-fun xprm () node)
(declare-fun height17 () Int)
(declare-fun height18 () Int)
(declare-fun height19 () Int)
(declare-fun size12 () Int)
(declare-fun size11 () Int)
(declare-fun x () node)
(declare-fun res () Int)
(declare-fun n () Int)
(declare-fun m () Int)


(assert 
(and 
;lexvar(= res v9prm)
(= v9prm height17)
(= xprm x)
(distinct xprm nil)
(= height17 n)
(<= height19 (+ 1 height18))
(<= height18 (+ 1 height19))
(= m (+ (+ size11 1) size12))
(tobool (ssep 
(pto xprm (sref (ref val Anon9) (ref height height17) (ref left p5) (ref right q5) ))
(avl p5 size12 height19)
(avl q5 size11 height18)
) )
)
)

(assert (not 
(exists ((m1 Int)(n1 Int))(and 
(= n1 n)
(= m1 m)
(= res n)
(<= 0 n)
(<= 0 m)
(tobool  
(avl x m1 n1)
 )
))
))

(check-sat)