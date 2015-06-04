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























































































































































































































































































































































































































































(declare-fun p11 () node)
(declare-fun q11 () node)
(declare-fun m () Int)
(declare-fun size24 () Int)
(declare-fun size23 () Int)
(declare-fun height31 () Int)
(declare-fun height32 () Int)
(declare-fun height33 () Int)
(declare-fun n () Int)
(declare-fun tmp1prm () node)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun Anon15 () Int)
(declare-fun v39prm () Int)
(declare-fun aprm () Int)


(assert 
(and 
;lexvar(= m (+ (+ size23 1) size24))
(<= height32 (+ 1 height31))
(<= height31 (+ 1 height32))
(= height33 n)
(distinct xprm nil)
(= tmp1prm nil)
(= aprm a)
(= xprm x)
(= v39prm Anon15)
(< v39prm aprm)
(tobool (ssep 
(avl p11 size24 height31)
(pto xprm (sref (ref val Anon15) (ref height height33) (ref left p11) (ref right q11) ))
(avl q11 size23 height32)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)