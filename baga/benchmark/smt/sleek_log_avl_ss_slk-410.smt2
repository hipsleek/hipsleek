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























































































































































































































































































































































































































































(declare-fun Anon40 () Int)
(declare-fun v208prm () Int)
(declare-fun v207prm () Int)
(declare-fun height97 () Int)
(declare-fun h25 () Int)
(declare-fun hrprm () Int)
(declare-fun height96 () Int)
(declare-fun h23 () Int)
(declare-fun hlprm () Int)
(declare-fun right8 () node)
(declare-fun hltprm () Int)
(declare-fun left8 () node)
(declare-fun hr2 () Int)
(declare-fun left7 () node)
(declare-fun right7 () node)
(declare-fun k2prm () node)
(declare-fun p28 () node)
(declare-fun m51 () Int)
(declare-fun n55 () Int)
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
(declare-fun n48 () Int)
(declare-fun n49 () Int)
(declare-fun height93 () Int)
(declare-fun n54 () Int)
(declare-fun height94 () Int)
(declare-fun height95 () Int)
(declare-fun m50 () Int)
(declare-fun size64 () Int)
(declare-fun size63 () Int)
(declare-fun Anon41 () NUM)
(declare-fun Anon30 () NUM)
(declare-fun p32 () node)
(declare-fun p21 () node)
(declare-fun q32 () node)
(declare-fun p31 () node)
(declare-fun m54 () Int)
(declare-fun n58 () Int)
(declare-fun m52 () Int)
(declare-fun n56 () Int)
(declare-fun h24 () Int)
(declare-fun n60 () Int)
(declare-fun height98 () Int)
(declare-fun height99 () Int)
(declare-fun m56 () Int)
(declare-fun size66 () Int)
(declare-fun size65 () Int)
(declare-fun Anon42 () node)
(declare-fun Anon37 () node)
(declare-fun p33 () node)
(declare-fun q31 () node)
(declare-fun q33 () node)
(declare-fun q28 () node)
(declare-fun m53 () Int)
(declare-fun n57 () Int)
(declare-fun m55 () Int)
(declare-fun n59 () Int)
(declare-fun hprm () Int)
(declare-fun n61 () Int)
(declare-fun height100 () Int)
(declare-fun height101 () Int)
(declare-fun m57 () Int)
(declare-fun size68 () Int)
(declare-fun size67 () Int)


(assert 
(and 
;lexvar(<= 0 n61)
(<= 0 m57)
(= v208prm n61)
(distinct k1prm nil)
(<= 0 n57)
(<= 0 m53)
(<= 0 n59)
(<= 0 m55)
(<= 0 n60)
(<= 0 m56)
(= v207prm n60)
(distinct xprm nil)
(<= 0 n58)
(<= 0 m54)
(<= 0 n56)
(<= 0 m52)
(= height97 height84)
(= hprm (+ 1 h25))
;eqmax(= hrprm n59)
(<= 0 n55)
(<= 0 m51)
(= n59 n55)
(= m55 m51)
(= height96 height63)
(= h24 (+ 1 h23))
;eqmax(= hlprm n58)
(<= 0 n47)
(<= 0 m43)
(= n58 n47)
(= m54 m43)
(= right8 q31)
(= hltprm n57)
(<= 0 height94)
(<= 0 size63)
(= n57 height94)
(= m53 size63)
(= left8 p31)
(= hr2 n56)
(<= 0 height95)
(<= 0 size64)
(= n56 height95)
(= m52 size64)
(= left7 p28)
(= right7 v13)
(= k2prm p28)
(<= 0 n48)
(<= 0 m44)
(= n55 n48)
(= m51 m44)
(= (+ n55 1) n54)
(<= 0 n54)
(<= 0 m50)
(<= 0 n49)
(<= 0 m45)
(= n54 n49)
(= m50 m45)
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
(<= n48 n49)
(= height93 n54)
(<= height95 (+ 1 height94))
(<= height94 (+ 1 height95))
(= m50 (+ (+ size63 1) size64))
(= Anon41 Anon30)
(= p32 p21)
(= q32 p31)
(= size66 m54)
(= height98 n58)
(= size65 m52)
(= height99 n56)
(<= height98 (+ 1 height99))
(<= height99 (+ 1 height98))
(= h24 n60)
(= m56 (+ (+ size65 1) size66))
(= Anon42 Anon37)
(= p33 q31)
(= q33 q28)
(= size68 m53)
(= height100 n57)
(= size67 m55)
(= height101 n59)
(<= height100 (+ 1 height101))
(<= height101 (+ 1 height100))
(= hprm n61)
(= m57 (+ (+ size67 1) size68))
(tobool (ssep 
(pto k2prm (sref (ref val Anon40) (ref height height93) (ref left xprm) (ref right k1prm) ))
(avl xprm m56 n60)
(avl k1prm m57 n61)
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