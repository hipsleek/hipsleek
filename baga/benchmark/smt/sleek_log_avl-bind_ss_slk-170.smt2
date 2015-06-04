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

(define-fun avl ((?in node) (?m Int) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?m 0)
(= ?n 0)

)(exists ((?n_33 Int))(and 
(= ?m (+ (+ ?m2 1) ?m1))
(<= (+ 0 ?n2) (+ ?n1 1))
(<= ?n1 (+ 1 ?n2))
(= ?n_33 ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref height ?n_33) (ref left ?p) (ref right ?q) ))
(avl ?p ?m1 ?n1)
(avl ?q ?m2 ?n2)
) )
)))))











































































































































































(declare-fun Anon27 () Int)
(declare-fun p19 () node)
(declare-fun q19 () node)
(declare-fun Anon_3947 () Int)
(declare-fun p17 () node)
(declare-fun q17 () node)
(declare-fun p11 () node)
(declare-fun xright_15089 () node)
(declare-fun n79 () Int)
(declare-fun n69 () Int)
(declare-fun Anon15 () Int)
(declare-fun n43 () Int)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun xright () node)
(declare-fun q11 () node)
(declare-fun m34 () Int)
(declare-fun n42 () Int)
(declare-fun m51 () Int)
(declare-fun n63 () Int)
(declare-fun flted21 () Int)
(declare-fun Anon23 () Int)
(declare-fun m52 () Int)
(declare-fun m35 () Int)
(declare-fun n41 () Int)
(declare-fun n64 () Int)
(declare-fun m56 () Int)
(declare-fun n70 () Int)
(declare-fun m57 () Int)
(declare-fun n71 () Int)
(declare-fun m59 () Int)
(declare-fun n73 () Int)
(declare-fun m60 () Int)
(declare-fun n74 () Int)
(declare-fun m58 () Int)
(declare-fun n72 () Int)
(declare-fun m61 () Int)
(declare-fun n75 () Int)
(declare-fun m64 () Int)
(declare-fun n80 () Int)
(declare-fun m65 () Int)
(declare-fun n81 () Int)
(declare-fun m53 () Int)
(declare-fun n65 () Int)
(declare-fun flted30_15091 () Int)
(declare-fun flted29_15090 () Int)
(declare-fun am () Int)
(declare-fun an () Int)
(declare-fun bm () Int)
(declare-fun bn () Int)
(declare-fun cm () Int)
(declare-fun cn () Int)
(declare-fun dm () Int)
(declare-fun v81prm () node)
(declare-fun res () node)
(declare-fun n () Int)
(declare-fun m () Int)


(assert 
(exists ((xrightprm node)(flted29 Int)(flted30 Int))(and 
;lexvar(= m60 (+ (+ m64 1) m65))
(<= (+ 0 n80) (+ n81 1))
(<= n81 (+ 1 n80))
(= n79 n74)
(<= n72 n73)
(= m52 (+ (+ m56 1) m57))
(<= (+ 0 n70) (+ n71 1))
(<= n71 (+ 1 n70))
(= n69 n64)
(< Anon15 aprm)
(= m (+ (+ m34 1) m35))
(<= (+ 0 n42) (+ n41 1))
(<= n41 (+ 1 n42))
(= n43 n)
(distinct xprm nil)
(= aprm a)
(= xprm x)
(= xright q11)
(= m51 m34)
(= n63 n42)
(<= 0 m34)
(<= 0 n42)
(= flted21 (+ 1 m51))
(<= 0 m51)
(<= 0 n63)
(= m52 flted21)
(= n64 Anon23)
(<= 0 flted21)
(<= 0 Anon23)
(<= 0 m52)
(<= 0 n64)
(= m53 m35)
(= n65 n41)
(<= 0 m35)
(<= 0 n41)
(= (+ 2 n65) n64)
(= m58 m56)
(= n72 n70)
(<= 0 m56)
(<= 0 n70)
(= m59 m57)
(= n73 n71)
(<= 0 m57)
(<= 0 n71)
(= m60 m59)
(= n74 n73)
(<= 0 m59)
(<= 0 n73)
(<= 0 m60)
(<= 0 n74)
(= (+ n75 1) n74)
(= m61 m58)
(= n75 n72)
(<= 0 m58)
(<= 0 n72)
(= am m53)
(= an n65)
(= bm m65)
(= bn n81)
(= cm m64)
(= cn n80)
(= dm m61)
(<= 0 m61)
(<= 0 n75)
(<= 0 m64)
(<= 0 n80)
(<= 0 m65)
(<= 0 n81)
(<= 0 m53)
(<= 0 n65)
(= flted30 (+ (+ (+ (+ dm bm) 3) am) cm))
(= flted29 (+ an 2))
(<= 0 am)
(<= 0 an)
(<= 0 bm)
(<= 0 bn)
(<= 0 cm)
(<= 0 cn)
(<= 0 dm)
(= res v81prm)
(tobool (ssep 
(pto p17 (sref (ref val Anon27) (ref height n79) (ref left p19) (ref right q19) ))
(avl v81prm flted30 flted29)
(pto xrightprm (sref (ref val Anon_3947) (ref height n69) (ref left p17) (ref right q17) ))
(pto xprm (sref (ref val Anon15) (ref height n43) (ref left p11) (ref right xrightprm) ))
) )
))
)

(assert (not 
(exists ((flted22 Int)(Anon28 Int))(and 
(= flted22 (+ 1 m))
(<= 0 n)
(<= 0 m)
(tobool  
(avl res flted22 Anon28)
 )
))
))

(check-sat)