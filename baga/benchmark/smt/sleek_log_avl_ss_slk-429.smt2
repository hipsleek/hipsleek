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























































































































































































































































































































































































































































(declare-fun Anon43_50668 () Int)
(declare-fun p34_50669 () node)
(declare-fun q34_50672 () node)
(declare-fun s2 () Int)
(declare-fun h2 () Int)
(declare-fun t2prm () node)
(declare-fun t2 () node)
(declare-fun t1 () node)
(declare-fun t1prm () node)
(declare-fun height106_50667 () Int)
(declare-fun h1 () Int)
(declare-fun height108_50674 () Int)
(declare-fun height107_50671 () Int)
(declare-fun s1 () Int)
(declare-fun size69_50670 () Int)
(declare-fun size70_50673 () Int)


(assert 
(exists ((height106 Int)(Anon43 Int)(p34 node)(size69 Int)(height107 Int)(q34 node)(size70 Int)(height108 Int))(and 
;lexvar(= t1prm t1)
(= t2prm t2)
(distinct t1 nil)
(distinct t1prm nil)
(= height106 h1)
(<= height107 (+ 1 height108))
(<= height108 (+ 1 height107))
(= s1 (+ (+ size70 1) size69))
(tobool (ssep 
(pto t1prm (sref (ref val Anon43) (ref height height106) (ref left p34) (ref right q34) ))
(avl p34 size69 height107)
(avl q34 size70 height108)
(avl t2 s2 h2)
) )
))
)

(assert (not 
(and 
(tobool  
(pto t1prm (sref (ref val val123prm) (ref height height123prm) (ref left left123prm) (ref right right123prm) ))
 )
)
))

(check-sat)