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























































































































































































































































































































































































































































(declare-fun Anon36_35151 () Int)
(declare-fun p27_35152 () node)
(declare-fun q27_35155 () node)
(declare-fun p21 () node)
(declare-fun k1prm () node)
(declare-fun v13 () node)
(declare-fun n47 () Int)
(declare-fun m43 () Int)
(declare-fun right5 () node)
(declare-fun n45 () Int)
(declare-fun flted34 () Int)
(declare-fun n43 () Int)
(declare-fun m41 () Int)
(declare-fun tmpprm () node)
(declare-fun q21 () node)
(declare-fun x () node)
(declare-fun a () Int)
(declare-fun tmp1prm () node)
(declare-fun xprm () node)
(declare-fun height63 () Int)
(declare-fun n () Int)
(declare-fun height62 () Int)
(declare-fun height61 () Int)
(declare-fun m () Int)
(declare-fun size44 () Int)
(declare-fun size43 () Int)
(declare-fun Anon30 () Int)
(declare-fun aprm () Int)
(declare-fun height81_35150 () Int)
(declare-fun n46 () Int)
(declare-fun height83_35157 () Int)
(declare-fun height82_35154 () Int)
(declare-fun m42 () Int)
(declare-fun size55_35153 () Int)
(declare-fun size56_35156 () Int)


(assert 
(exists ((height81 Int)(Anon36 Int)(p27 node)(size55 Int)(height82 Int)(q27 node)(size56 Int)(height83 Int))(and 
;lexvar(= k1prm v13)
(= (+ 2 n47) n46)
(<= 0 n47)
(<= 0 m43)
(<= 0 height61)
(<= 0 size44)
(= n47 height61)
(= m43 size44)
(<= 0 n46)
(<= 0 m42)
(<= 0 n45)
(<= 0 flted34)
(= n46 n45)
(= m42 flted34)
(= right5 q21)
(<= 0 n43)
(<= 0 m41)
(<= n45 (+ 1 n43))
(<= n43 n45)
(= flted34 (+ 1 m41))
(<= 0 height62)
(<= 0 size43)
(= n43 height62)
(= m41 size43)
(= tmpprm q21)
(= xprm x)
(= aprm a)
(= tmp1prm nil)
(distinct xprm nil)
(= height63 n)
(<= height61 (+ 1 height62))
(<= height62 (+ 1 height61))
(= m (+ (+ size43 1) size44))
(< Anon30 aprm)
(= height81 n46)
(<= height82 (+ 1 height83))
(<= height83 (+ 1 height82))
(= m42 (+ (+ size56 1) size55))
(tobool (ssep 
(pto xprm (sref (ref val Anon30) (ref height height63) (ref left p21) (ref right v13) ))
(pto k1prm (sref (ref val Anon36) (ref height height81) (ref left p27) (ref right q27) ))
(avl p27 size55 height82)
(avl q27 size56 height83)
(avl p21 m43 n47)
) )
))
)

(assert (not 
(and 
(tobool  
(pto k1prm (sref (ref val val97prm) (ref height height97prm) (ref left left97prm) (ref right right97prm) ))
 )
)
))

(check-sat)