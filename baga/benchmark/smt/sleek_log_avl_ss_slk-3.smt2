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























































































































































































































































































































































































































































(declare-fun Anon_89 () Int)
(declare-fun p_90 () node)
(declare-fun q_93 () node)
(declare-fun my () Int)
(declare-fun mx () Int)
(declare-fun size1_91 () Int)
(declare-fun size2_94 () Int)
(declare-fun height2_92 () Int)
(declare-fun height3_95 () Int)
(declare-fun height1_88 () Int)
(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun nx1_96 () Int)
(declare-fun nx () Int)
(declare-fun vprm () Int)


(assert 
(exists ((height1 Int)(Anon Int)(p node)(size1 Int)(height2 Int)(q node)(size2 Int)(height3 Int)(nx1 Int))(and 
;lexvar(= mx (+ (+ size2 1) size1))
(<= height3 (+ 1 height2))
(<= height2 (+ 1 height3))
(= height1 nx)
(= xprm x)
(= yprm y)
(distinct x nil)
(= nx1 nx)
(= vprm 0)
(tobool (ssep 
(pto xprm (sref (ref val Anon) (ref height height1) (ref left p) (ref right q) ))
(avl p size1 height2)
(avl q size2 height3)
(avl y my nx1)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val valprm) (ref height heightprm) (ref left leftprm) (ref right rightprm) ))
 )
)
))

(check-sat)