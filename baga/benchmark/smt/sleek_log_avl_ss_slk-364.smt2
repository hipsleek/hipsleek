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























































































































































































































































































































































































































































(declare-fun Anon37 () Int)
(declare-fun q28 () node)
(declare-fun v191prm () Int)
(declare-fun hprm () Int)
(declare-fun hrprm () Int)
(declare-fun n52 () Int)
(declare-fun m48 () Int)
(declare-fun height87 () Int)
(declare-fun h20 () Int)
(declare-fun hlprm () Int)
(declare-fun left6 () node)
(declare-fun hr1 () Int)
(declare-fun right6 () node)
(declare-fun m45 () Int)
(declare-fun m44 () Int)
(declare-fun k1prm () node)
(declare-fun v13 () node)
(declare-fun n47 () Int)
(declare-fun m43 () Int)
(declare-fun right5 () node)
(declare-fun n45 () Int)
(declare-fun flted34 () Int)
(declare-fun n43 () Int)
(declare-fun m41 () Int)
(declare-fun tmpprm () node)
(declare-fun q21 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun a () NUM)
(declare-fun tmp1prm () node)
(declare-fun height63 () Int)
(declare-fun n () Int)
(declare-fun height62 () Int)
(declare-fun height61 () Int)
(declare-fun m () Int)
(declare-fun size44 () Int)
(declare-fun size43 () Int)
(declare-fun aprm () NUM)
(declare-fun height84 () Int)
(declare-fun n46 () Int)
(declare-fun height85 () Int)
(declare-fun height86 () Int)
(declare-fun m42 () Int)
(declare-fun size58 () Int)
(declare-fun size57 () Int)
(declare-fun n49 () Int)
(declare-fun n48 () Int)
(declare-fun Anon38 () NUM)
(declare-fun Anon30 () NUM)
(declare-fun p29 () node)
(declare-fun p21 () node)
(declare-fun q29 () node)
(declare-fun p28 () node)
(declare-fun m47 () Int)
(declare-fun n51 () Int)
(declare-fun m46 () Int)
(declare-fun n50 () Int)
(declare-fun h21 () Int)
(declare-fun n53 () Int)
(declare-fun height88 () Int)
(declare-fun height89 () Int)
(declare-fun m49 () Int)
(declare-fun size60 () Int)
(declare-fun size59 () Int)


(assert 
(and 
;lexvar(= v191prm 1)
;eqmax(<= 0 n53)
(<= 0 m49)
(distinct xprm nil)
(<= 0 n51)
(<= 0 m47)
(<= 0 n50)
(<= 0 m46)
(<= 0 n52)
(<= 0 m48)
(= hrprm n52)
(<= 0 n48)
(<= 0 m44)
(= n52 n48)
(= m48 m44)
(= height87 height63)
(= h21 (+ 1 h20))
;eqmax(= hlprm n51)
(<= 0 n47)
(<= 0 m43)
(= n51 n47)
(= m47 m43)
(= left6 p28)
(= hr1 n50)
(<= 0 n49)
(<= 0 m45)
(= n50 n49)
(= m46 m45)
(= right6 v13)
(<= 0 height86)
(<= 0 size58)
(= n49 height86)
(= m45 size58)
(<= 0 height85)
(<= 0 size57)
(= n48 height85)
(= m44 size57)
(= k1prm v13)
(= (+ 2 n47) n46)
(<= 0 height61)
(<= 0 size44)
(= n47 height61)
(= m43 size44)
(<= 0 n46)
(<= 0 m42)
(<= 0 n45)
(<= 0 flted34)
(= n46 n45)
(= m42 flted34)
(= right5 q21)
(<= 0 n43)
(<= 0 m41)
(<= n45 (+ 1 n43))
(<= n43 n45)
(= flted34 (+ 1 m41))
(<= 0 height62)
(<= 0 size43)
(= n43 height62)
(= m41 size43)
(= tmpprm q21)
(= xprm x)
(= aprm a)
(= tmp1prm nil)
(= height63 n)
(<= height61 (+ 1 height62))
(<= height62 (+ 1 height61))
(= m (+ (+ size43 1) size44))
(< Anon30 aprm)
(= height84 n46)
(<= height86 (+ 1 height85))
(<= height85 (+ 1 height86))
(= m42 (+ (+ size57 1) size58))
(< n49 n48)
(= Anon38 Anon30)
(= p29 p21)
(= q29 p28)
(= size60 m47)
(= height88 n51)
(= size59 m46)
(= height89 n50)
(<= height88 (+ 1 height89))
(<= height89 (+ 1 height88))
(= h21 n53)
(= m49 (+ (+ size59 1) size60))
(tobool (ssep 
(pto k1prm (sref (ref val Anon37) (ref height height84) (ref left xprm) (ref right q28) ))
(avl q28 m48 n52)
(avl xprm m49 n53)
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