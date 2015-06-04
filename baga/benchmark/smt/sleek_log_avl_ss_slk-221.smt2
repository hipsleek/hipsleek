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























































































































































































































































































































































































































































(declare-fun Anon29_20045 () Int)
(declare-fun p20_20046 () node)
(declare-fun q20_20049 () node)
(declare-fun x () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun tmp1prm () node)
(declare-fun xprm () node)
(declare-fun height58_20044 () Int)
(declare-fun n () Int)
(declare-fun height60_20051 () Int)
(declare-fun height59_20048 () Int)
(declare-fun m () Int)
(declare-fun size41_20047 () Int)
(declare-fun size42_20050 () Int)


(assert 
(exists ((height58 Int)(Anon29 Int)(p20 node)(size41 Int)(height59 Int)(q20 node)(size42 Int)(height60 Int))(and 
;lexvar(= xprm x)
(= aprm a)
(= tmp1prm nil)
(distinct xprm nil)
(= height58 n)
(<= height59 (+ 1 height60))
(<= height60 (+ 1 height59))
(= m (+ (+ size42 1) size41))
(tobool (ssep 
(pto xprm (sref (ref val Anon29) (ref height height58) (ref left p20) (ref right q20) ))
(avl p20 size41 height59)
(avl q20 size42 height60)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val59prm) (ref height height59prm) (ref left left59prm) (ref right right59prm) ))
 )
)
))

(check-sat)