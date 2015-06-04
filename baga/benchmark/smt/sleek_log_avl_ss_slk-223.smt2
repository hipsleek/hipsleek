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
(declare-fun q21 () node)
(declare-fun m () Int)
(declare-fun size44 () Int)
(declare-fun size43 () Int)
(declare-fun height61 () Int)
(declare-fun height62 () Int)
(declare-fun height63 () Int)
(declare-fun n () Int)
(declare-fun tmp1prm () node)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun Anon30 () Int)
(declare-fun v130prm () Int)
(declare-fun aprm () Int)


(assert 
(and 
;lexvar(= m (+ (+ size43 1) size44))
(<= height62 (+ 1 height61))
(<= height61 (+ 1 height62))
(= height63 n)
(distinct xprm nil)
(= tmp1prm nil)
(= aprm a)
(= xprm x)
(= v130prm Anon30)
(< v130prm aprm)
(tobool (ssep 
(avl p21 size44 height61)
(pto xprm (sref (ref val Anon30) (ref height height63) (ref left p21) (ref right q21) ))
(avl q21 size43 height62)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)