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























































































































































































































































































































































































































































(declare-fun Anon14_6346 () Int)
(declare-fun p10_6347 () node)
(declare-fun q10_6350 () node)
(declare-fun x () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun tmp1prm () node)
(declare-fun xprm () node)
(declare-fun height28_6345 () Int)
(declare-fun n () Int)
(declare-fun height30_6352 () Int)
(declare-fun height29_6349 () Int)
(declare-fun m () Int)
(declare-fun size21_6348 () Int)
(declare-fun size22_6351 () Int)


(assert 
(exists ((height28 Int)(Anon14 Int)(p10 node)(size21 Int)(height29 Int)(q10 node)(size22 Int)(height30 Int))(and 
;lexvar(= xprm x)
(= aprm a)
(= tmp1prm nil)
(distinct xprm nil)
(= height28 n)
(<= height29 (+ 1 height30))
(<= height30 (+ 1 height29))
(= m (+ (+ size22 1) size21))
(tobool (ssep 
(pto xprm (sref (ref val Anon14) (ref height height28) (ref left p10) (ref right q10) ))
(avl p10 size21 height29)
(avl q10 size22 height30)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val6prm) (ref height height6prm) (ref left left6prm) (ref right right6prm) ))
 )
)
))

(check-sat)