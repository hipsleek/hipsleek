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























































































































































































































































































































































































































































(declare-fun Anon8_841 () Int)
(declare-fun p4_842 () node)
(declare-fun q4_845 () node)
(declare-fun x () node)
(declare-fun xprm () node)
(declare-fun height14_840 () Int)
(declare-fun n () Int)
(declare-fun height16_847 () Int)
(declare-fun height15_844 () Int)
(declare-fun m () Int)
(declare-fun size9_843 () Int)
(declare-fun size10_846 () Int)


(assert 
(exists ((height14 Int)(Anon8 Int)(p4 node)(size9 Int)(height15 Int)(q4 node)(size10 Int)(height16 Int))(and 
;lexvar(= xprm x)
(distinct xprm nil)
(= height14 n)
(<= height15 (+ 1 height16))
(<= height16 (+ 1 height15))
(= m (+ (+ size10 1) size9))
(tobool (ssep 
(pto xprm (sref (ref val Anon8) (ref height height14) (ref left p4) (ref right q4) ))
(avl p4 size9 height15)
(avl q4 size10 height16)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val5prm) (ref height height5prm) (ref left left5prm) (ref right right5prm) ))
 )
)
))

(check-sat)