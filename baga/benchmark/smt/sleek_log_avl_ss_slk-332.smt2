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























































































































































































































































































































































































































































(declare-fun v13 () node)
(declare-fun p21 () node)
(declare-fun Anon30 () Int)
(declare-fun m () Int)
(declare-fun height63 () Int)
(declare-fun n () Int)
(declare-fun tmp1prm () node)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun tmpprm () node)
(declare-fun size43 () Int)
(declare-fun height62 () Int)
(declare-fun m41 () Int)
(declare-fun n43 () Int)
(declare-fun right5 () node)
(declare-fun q21 () node)
(declare-fun flted34 () Int)
(declare-fun n45 () Int)
(declare-fun m42 () Int)
(declare-fun size44 () Int)
(declare-fun height61 () Int)
(declare-fun m43 () Int)
(declare-fun n47 () Int)
(declare-fun n46 () Int)
(declare-fun v177prm () Int)
(declare-fun v178prm () Int)


(assert 
(and 
;lexvar(< Anon30 aprm)
(= m (+ (+ size43 1) size44))
(<= height62 (+ 1 height61))
(<= height61 (+ 1 height62))
(= height63 n)
(distinct xprm nil)
(= tmp1prm nil)
(= aprm a)
(= xprm x)
(= tmpprm q21)
(= m41 size43)
(= n43 height62)
(<= 0 size43)
(<= 0 height62)
(= flted34 (+ 1 m41))
(<= n43 n45)
(<= n45 (+ 1 n43))
(<= 0 m41)
(<= 0 n43)
(= right5 q21)
(= m42 flted34)
(= n46 n45)
(<= 0 flted34)
(<= 0 n45)
(<= 0 m42)
(<= 0 n46)
(= m43 size44)
(= n47 height61)
(<= 0 size44)
(<= 0 height61)
(<= 0 m43)
(<= 0 n47)
(= (+ v177prm n47) n46)
(= v178prm 2)
(= v177prm v178prm)
(tobool (ssep 
(avl v13 m42 n46)
(pto xprm (sref (ref val Anon30) (ref height height63) (ref left p21) (ref right v13) ))
(avl p21 m43 n47)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)