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























































































































































































































































































































































































































































(declare-fun Anon44 () Int)
(declare-fun q35 () node)
(declare-fun Anon46 () Int)
(declare-fun size72 () Int)
(declare-fun size71 () Int)
(declare-fun height111 () Int)
(declare-fun height110 () Int)
(declare-fun height109 () Int)
(declare-fun h1 () Int)
(declare-fun t2prm () node)
(declare-fun t2 () node)
(declare-fun t1prm () node)
(declare-fun t1 () node)
(declare-fun h2 () Int)
(declare-fun flted37 () Int)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun v215prm () node)
(declare-fun p35 () node)
(declare-fun tmpprm () node)
(declare-fun s1 () Int)
(declare-fun s2 () Int)


(assert 
(and 
;lexvar(= s1 (+ (+ size71 1) size72))
(<= height110 (+ 1 height111))
(<= height111 (+ 1 height110))
(= height109 h1)
(distinct t1prm nil)
(distinct t1 nil)
(= t2prm t2)
(= t1prm t1)
(= m s2)
(= n h2)
(<= 0 s2)
(<= 0 h2)
(= flted37 (+ 1 m))
(<= 0 m)
(<= 0 n)
(= v215prm p35)
(distinct tmpprm nil)
(tobool (ssep 
(pto t1prm (sref (ref val Anon44) (ref height height109) (ref left p35) (ref right q35) ))
(avl p35 size72 height111)
(avl q35 size71 height110)
(avl tmpprm flted37 Anon46)
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(avl tmpprm s1 h29)
(avl v215prm s2 h30)
) )
)
))

(check-sat)