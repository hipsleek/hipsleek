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























































































































































































































































































































































































































































(declare-fun q21 () node)
(declare-fun Anon32 () Int)
(declare-fun Anon34 () Int)
(declare-fun n40 () Int)
(declare-fun m38 () Int)
(declare-fun v165prm () node)
(declare-fun p23 () node)
(declare-fun right4 () node)
(declare-fun q25 () node)
(declare-fun hltprm () Int)
(declare-fun n39 () Int)
(declare-fun m37 () Int)
(declare-fun left5 () node)
(declare-fun p25 () node)
(declare-fun hrprm () Int)
(declare-fun n38 () Int)
(declare-fun m36 () Int)
(declare-fun right3 () node)
(declare-fun left4 () node)
(declare-fun k2prm () node)
(declare-fun q23 () node)
(declare-fun n36 () Int)
(declare-fun m34 () Int)
(declare-fun m30 () Int)
(declare-fun m29 () Int)
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
(declare-fun height67 () Int)
(declare-fun n29 () Int)
(declare-fun height68 () Int)
(declare-fun height69 () Int)
(declare-fun m27 () Int)
(declare-fun size48 () Int)
(declare-fun size47 () Int)
(declare-fun n31 () Int)
(declare-fun n32 () Int)
(declare-fun height74 () Int)
(declare-fun n37 () Int)
(declare-fun height75 () Int)
(declare-fun height76 () Int)
(declare-fun m35 () Int)
(declare-fun size52 () Int)
(declare-fun size51 () Int)


(assert 
(and 
;lexvar(= n40 n36)
(= m38 m34)
(= v165prm p23)
(= right4 q25)
(<= 0 n39)
(<= 0 m37)
(= hltprm n39)
(<= 0 height75)
(<= 0 size51)
(= n39 height75)
(= m37 size51)
(= left5 p25)
(<= 0 n38)
(<= 0 m36)
(= hrprm n38)
(<= 0 height76)
(<= 0 size52)
(= n38 height76)
(= m36 size52)
(= right3 q23)
(= left4 v9)
(= k2prm q23)
(= (+ n36 1) n37)
(<= 0 n37)
(<= 0 m35)
(<= 0 n32)
(<= 0 m30)
(= n37 n32)
(= m35 m30)
(<= 0 n36)
(<= 0 m34)
(<= 0 n31)
(<= 0 m29)
(= n36 n31)
(= m34 m29)
(<= 0 height68)
(<= 0 size47)
(= n32 height68)
(= m30 size47)
(<= 0 height69)
(<= 0 size48)
(= n31 height69)
(= m29 size48)
(= k1prm v9)
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
(= height67 n29)
(<= height69 (+ 1 height68))
(<= height68 (+ 1 height69))
(= m27 (+ (+ size47 1) size48))
(<= n31 n32)
(= height74 n37)
(<= height76 (+ 1 height75))
(<= height75 (+ 1 height76))
(= m35 (+ (+ size51 1) size52))
(tobool (ssep 
(avl q21 m28 n30)
(pto xprm (sref (ref val Anon30) (ref height height63) (ref left q25) (ref right q21) ))
(pto k1prm (sref (ref val Anon32) (ref height height67) (ref left p23) (ref right p25) ))
(avl p25 m36 n38)
(avl q25 m37 n39)
(pto k2prm (sref (ref val Anon34) (ref height height74) (ref left k1prm) (ref right xprm) ))
) )
)
)

(assert (not 
;lexvar
))

(check-sat)