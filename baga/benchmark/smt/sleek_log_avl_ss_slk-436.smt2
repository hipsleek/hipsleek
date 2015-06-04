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
(declare-fun p35 () node)
(declare-fun Anon48 () Int)
(declare-fun n () Int)
(declare-fun h2 () Int)
(declare-fun m () Int)
(declare-fun t2prm () node)
(declare-fun t2 () node)
(declare-fun t1 () node)
(declare-fun t1prm () node)
(declare-fun height109 () Int)
(declare-fun h1 () Int)
(declare-fun height110 () Int)
(declare-fun size71 () Int)
(declare-fun size72 () Int)
(declare-fun height111 () Int)
(declare-fun flted37 () Int)
(declare-fun Anon46 () Int)
(declare-fun flted39 () Int)
(declare-fun tmpprm () node)
(declare-fun s1 () Int)
(declare-fun h29 () Int)
(declare-fun s2 () Int)
(declare-fun h30 () Int)
(declare-fun v216prm () node)
(declare-fun q35 () node)
(declare-fun tmp1prm () node)


(assert 
(and 
;lexvar(<= 0 n)
(<= 0 m)
(= flted37 (+ 1 m))
(<= 0 h2)
(<= 0 s2)
(= n h2)
(= m s2)
(= t1prm t1)
(= t2prm t2)
(distinct t1 nil)
(distinct t1prm nil)
(= height109 h1)
(<= height111 (+ 1 height110))
(<= height110 (+ 1 height111))
(= s1 (+ (+ size71 1) size72))
(= s1 flted37)
(= h29 Anon46)
(= s2 size72)
(= h30 height111)
(<= 0 size72)
(<= 0 height111)
(<= 0 flted37)
(<= 0 Anon46)
(= flted39 (+ s2 s1))
(distinct tmpprm nil)
(<= 0 s1)
(<= 0 h29)
(<= 0 s2)
(<= 0 h30)
(= v216prm q35)
(distinct tmp1prm nil)
(tobool (ssep 
(pto t1prm (sref (ref val Anon44) (ref height height109) (ref left p35) (ref right q35) ))
(avl q35 size71 height110)
(avl tmp1prm flted39 Anon48)
) )
)
)

(assert (not 
(and 
(tobool (ssep 
(avl tmp1prm s3 h31)
(avl v216prm s4 h32)
) )
)
))

(check-sat)