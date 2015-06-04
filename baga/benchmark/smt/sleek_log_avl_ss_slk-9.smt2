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























































































































































































































































































































































































































































(declare-fun Anon6_422 () Int)
(declare-fun p2_423 () node)
(declare-fun q2_426 () node)
(declare-fun mz () Int)
(declare-fun Anon2 () Int)
(declare-fun Anon3 () Int)
(declare-fun right () node)
(declare-fun Anon5 () node)
(declare-fun left () node)
(declare-fun Anon4 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun yprm () node)
(declare-fun zprm () node)
(declare-fun z () node)
(declare-fun y () node)
(declare-fun ny2 () Int)
(declare-fun height7_421 () Int)
(declare-fun ny () Int)
(declare-fun height9_428 () Int)
(declare-fun height8_425 () Int)
(declare-fun my () Int)
(declare-fun size5_424 () Int)
(declare-fun size6_427 () Int)


(assert 
(exists ((height7 Int)(Anon6 Int)(p2 node)(size5 Int)(height8 Int)(q2 node)(size6 Int)(height9 Int))(and 
;lexvar(= right Anon5)
(= left Anon4)
(= xprm x)
(= yprm y)
(= zprm z)
(distinct y nil)
(= ny2 ny)
(= height7 ny)
(<= height8 (+ 1 height9))
(<= height9 (+ 1 height8))
(= my (+ (+ size6 1) size5))
(tobool (ssep 
(pto yprm (sref (ref val Anon6) (ref height height7) (ref left p2) (ref right q2) ))
(avl p2 size5 height8)
(avl q2 size6 height9)
(avl z mz ny2)
(pto xprm (sref (ref val Anon2) (ref height Anon3) (ref left yprm) (ref right zprm) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto yprm (sref (ref val val3prm) (ref height height3prm) (ref left left3prm) (ref right right3prm) ))
 )
)
))

(check-sat)