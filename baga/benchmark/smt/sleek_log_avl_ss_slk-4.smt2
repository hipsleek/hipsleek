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























































































































































































































































































































































































































































(declare-fun Anon1 () Int)
(declare-fun p1 () node)
(declare-fun q1 () node)
(declare-fun my () Int)
(declare-fun v1prm () Int)
(declare-fun tmpprm () Int)
(declare-fun mx () Int)
(declare-fun size4 () Int)
(declare-fun size3 () Int)
(declare-fun height4 () Int)
(declare-fun height5 () Int)
(declare-fun height6 () Int)
(declare-fun xprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun x () node)
(declare-fun nx2 () Int)
(declare-fun nx () Int)
(declare-fun vprm () Int)


(assert 
(and 
;lexvar(= v1prm 1)
(= tmpprm height6)
(= mx (+ (+ size3 1) size4))
(<= height5 (+ 1 height4))
(<= height4 (+ 1 height5))
(= height6 nx)
(= xprm x)
(= yprm y)
(distinct x nil)
(= nx2 nx)
(= vprm 0)
(tobool (ssep 
(pto xprm (sref (ref val Anon1) (ref height height6) (ref left p1) (ref right q1) ))
(avl p1 size4 height4)
(avl q1 size3 height5)
(avl y my nx2)
) )
)
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)