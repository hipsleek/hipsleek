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























































































































































































































































































































































































































































(declare-fun p35 () node)
(declare-fun q35 () node)
(declare-fun n () node)
(declare-fun h2 () node)
(declare-fun m () node)
(declare-fun s2 () node)
(declare-fun v214prm () Int)
(declare-fun Anon44 () Int)
(declare-fun t2prm () node)
(declare-fun t2 () node)
(declare-fun t1 () node)
(declare-fun t1prm () node)
(declare-fun height109 () Int)
(declare-fun h1 () Int)
(declare-fun height110 () Int)
(declare-fun height111 () Int)
(declare-fun s1 () Int)
(declare-fun size72 () Int)
(declare-fun size71 () Int)


(assert 
(and 
;lexvar(= n h2)
(= m s2)
(= v214prm Anon44)
(= t1prm t1)
(= t2prm t2)
(distinct t1 nil)
(distinct t1prm nil)
(= height109 h1)
(<= height111 (+ 1 height110))
(<= height110 (+ 1 height111))
(= s1 (+ (+ size71 1) size72))
(tobool (ssep 
(avl p35 size72 height111)
(pto t1prm (sref (ref val Anon44) (ref height height109) (ref left p35) (ref right q35) ))
(avl q35 size71 height110)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)