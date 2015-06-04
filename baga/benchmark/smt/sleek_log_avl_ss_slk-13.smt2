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























































































































































































































































































































































































































































(declare-fun Anon7 () Int)
(declare-fun p3 () node)
(declare-fun q3 () node)
(declare-fun Anon2 () Int)
(declare-fun height13 () node)
(declare-fun Anon3 () node)
(declare-fun v5_633 () Int)
(declare-fun right () node)
(declare-fun Anon5 () node)
(declare-fun left () node)
(declare-fun Anon4 () node)
(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun zprm () node)
(declare-fun z () node)
(declare-fun y () node)
(declare-fun ny2 () Int)
(declare-fun height10 () Int)
(declare-fun height11 () Int)
(declare-fun height12 () Int)
(declare-fun size8 () Int)
(declare-fun size7 () Int)
(declare-fun x () node)
(declare-fun mz () Int)
(declare-fun ny () Int)
(declare-fun my () Int)


(assert 
(exists ((v5prm Int))(and 
;lexvar(= height13 Anon3)
(= v5prm (+ 1 height10))
(= right Anon5)
(= left Anon4)
(= xprm x)
(= yprm y)
(= zprm z)
(distinct y nil)
(= ny2 ny)
(= height10 ny)
(<= height12 (+ 1 height11))
(<= height11 (+ 1 height12))
(= my (+ (+ size7 1) size8))
(tobool (ssep 
(pto yprm (sref (ref val Anon7) (ref height height10) (ref left p3) (ref right q3) ))
(avl p3 size8 height12)
(avl q3 size7 height11)
(avl z mz ny2)
(pto xprm (sref (ref val Anon2) (ref height v5prm) (ref left yprm) (ref right zprm) ))
) )
))
)

(assert (not 
(exists ((flted2 Int)(flted3 Int))(and 
(= flted2 (+ ny 1))
(= flted3 (+ (+ mz 1) my))
(<= 0 mz)
(<= 0 ny)
(<= 0 my)
(tobool  
(avl x flted3 flted2)
 )
))
))

(check-sat)