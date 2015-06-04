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
(declare-fun q35 () node)
(declare-fun Anon49_51222 () Int)
(declare-fun tmp_51223 () node)
(declare-fun h30 () Int)
(declare-fun h29 () Int)
(declare-fun Anon46 () Int)
(declare-fun size72 () Int)
(declare-fun height111 () Int)
(declare-fun height109 () Int)
(declare-fun t2prm () node)
(declare-fun t2 () node)
(declare-fun t1prm () node)
(declare-fun flted37 () Int)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun size71 () Int)
(declare-fun height110 () Int)
(declare-fun flted39 () Int)
(declare-fun Anon48 () Int)
(declare-fun flted40_51221 () Int)
(declare-fun tmp1_51224 () node)
(declare-fun s3 () Int)
(declare-fun h31 () Int)
(declare-fun s4 () Int)
(declare-fun h32 () Int)
(declare-fun v217prm () node)
(declare-fun res () node)
(declare-fun h2 () Int)
(declare-fun s2 () Int)
(declare-fun h1 () Int)
(declare-fun s1 () Int)
(declare-fun t1 () node)


(assert 
(exists ((flted40 Int)(Anon49 Int)(tmpprm Int)(tmp1prm Int))(and 
;lexvar(<= 0 h30)
(<= 0 s2)
(<= 0 h29)
(<= 0 s1)
(distinct tmpprm nil)
(= flted39 (+ s2 s1))
(<= 0 Anon46)
(<= 0 flted37)
(<= 0 height111)
(<= 0 size72)
(= h30 height111)
(= s2 size72)
(= h29 Anon46)
(= s1 flted37)
(= s1 (+ (+ size71 1) size72))
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
(= s3 flted39)
(= h31 Anon48)
(= s4 size71)
(= h32 height110)
(<= 0 size71)
(<= 0 height110)
(<= 0 flted39)
(<= 0 Anon48)
(= flted40 (+ s4 s3))
(distinct tmp1prm nil)
(<= 0 s3)
(<= 0 h31)
(<= 0 s4)
(<= 0 h32)
(= res v217prm)
(tobool (ssep 
(pto t1prm (sref (ref val Anon44) (ref height height109) (ref left p35) (ref right q35) ))
(avl v217prm flted40 Anon49)
) )
))
)

(assert (not 
(exists ((flted41 Int)(Anon50 Int))(and 
(= flted41 (+ s2 s1))
(<= 0 h2)
(<= 0 s2)
(<= 0 h1)
(<= 0 s1)
(distinct t1 nil)
(tobool  
(avl res flted41 Anon50)
 )
))
))

(check-sat)