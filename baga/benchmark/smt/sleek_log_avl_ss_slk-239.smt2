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























































































































































































































































































































































































































































(declare-fun Anon31_21144 () Int)
(declare-fun p22_21145 () node)
(declare-fun q22_21148 () node)
(declare-fun q21 () node)
(declare-fun k1prm () node)
(declare-fun v9 () node)
(declare-fun n30 () Int)
(declare-fun m28 () Int)
(declare-fun left2 () node)
(declare-fun n28 () Int)
(declare-fun flted32 () Int)
(declare-fun n26 () Int)
(declare-fun m26 () Int)
(declare-fun tmpprm () node)
(declare-fun p21 () node)
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
(declare-fun aprm () Int)
(declare-fun Anon30 () Int)
(declare-fun height64_21143 () Int)
(declare-fun n29 () Int)
(declare-fun height66_21150 () Int)
(declare-fun height65_21147 () Int)
(declare-fun m27 () Int)
(declare-fun size45_21146 () Int)
(declare-fun size46_21149 () Int)


(assert 
(exists ((height64 Int)(Anon31 Int)(p22 node)(size45 Int)(height65 Int)(q22 node)(size46 Int)(height66 Int))(and 
;lexvar(= k1prm v9)
(= (+ 2 n30) n29)
(<= 0 n30)
(<= 0 m28)
(<= 0 height62)
(<= 0 size43)
(= n30 height62)
(= m28 size43)
(<= 0 n29)
(<= 0 m27)
(<= 0 n28)
(<= 0 flted32)
(= n29 n28)
(= m27 flted32)
(= left2 p21)
(<= 0 n26)
(<= 0 m26)
(<= n28 (+ 1 n26))
(<= n26 n28)
(= flted32 (+ 1 m26))
(<= 0 height61)
(<= 0 size44)
(= n26 height61)
(= m26 size44)
(= tmpprm p21)
(= xprm x)
(= aprm a)
(= tmp1prm nil)
(distinct xprm nil)
(= height63 n)
(<= height61 (+ 1 height62))
(<= height62 (+ 1 height61))
(= m (+ (+ size43 1) size44))
(<= aprm Anon30)
(= height64 n29)
(<= height65 (+ 1 height66))
(<= height66 (+ 1 height65))
(= m27 (+ (+ size46 1) size45))
(tobool (ssep 
(pto xprm (sref (ref val Anon30) (ref height height63) (ref left v9) (ref right q21) ))
(pto k1prm (sref (ref val Anon31) (ref height height64) (ref left p22) (ref right q22) ))
(avl p22 size45 height65)
(avl q22 size46 height66)
(avl q21 m28 n30)
) )
))
)

(assert (not 
(and 
(tobool  
(pto k1prm (sref (ref val val65prm) (ref height height65prm) (ref left left65prm) (ref right right65prm) ))
 )
)
))

(check-sat)