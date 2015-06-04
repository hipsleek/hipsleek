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























































































































































































































































































































































































































































(declare-fun p21 () node)
(declare-fun v172prm () node)
(declare-fun n44_34304 () Int)
(declare-fun flted33_34303 () Int)
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


(assert 
(exists ((flted33 Int)(n44 Int))(and 
;lexvar(<= 0 n43)
(<= 0 m41)
(<= n44 (+ 1 n43))
(<= n43 n44)
(= flted33 (+ 1 m41))
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
(tobool (ssep 
(avl p21 size44 height61)
(pto xprm (sref (ref val Anon30) (ref height height63) (ref left p21) (ref right q21) ))
(avl v172prm flted33 n44)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val93prm) (ref height height93prm) (ref left left93prm) (ref right right93prm) ))
 )
)
))

(check-sat)