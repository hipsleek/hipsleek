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











































































































































































(declare-fun Anon21 () Int)
(declare-fun p15 () node)
(declare-fun q15 () node)
(declare-fun Anon_3699 () Int)
(declare-fun p13 () node)
(declare-fun q13 () node)
(declare-fun xleft_14716 () node)
(declare-fun q11 () node)
(declare-fun n60 () Int)
(declare-fun n50 () Int)
(declare-fun Anon15 () Int)
(declare-fun n43 () Int)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun xleft () node)
(declare-fun p11 () node)
(declare-fun m35 () Int)
(declare-fun n41 () Int)
(declare-fun m36 () Int)
(declare-fun n44 () Int)
(declare-fun flted19 () Int)
(declare-fun Anon17 () Int)
(declare-fun m37 () Int)
(declare-fun m34 () Int)
(declare-fun n42 () Int)
(declare-fun n45 () Int)
(declare-fun m42 () Int)
(declare-fun n52 () Int)
(declare-fun m41 () Int)
(declare-fun n51 () Int)
(declare-fun m43 () Int)
(declare-fun n53 () Int)
(declare-fun m44 () Int)
(declare-fun n54 () Int)
(declare-fun m46 () Int)
(declare-fun n56 () Int)
(declare-fun m38 () Int)
(declare-fun n46 () Int)
(declare-fun m49 () Int)
(declare-fun n61 () Int)
(declare-fun m50 () Int)
(declare-fun n62 () Int)
(declare-fun m45 () Int)
(declare-fun n55 () Int)
(declare-fun flted26_14718 () Int)
(declare-fun flted25_14717 () Int)
(declare-fun am () Int)
(declare-fun an () Int)
(declare-fun bm () Int)
(declare-fun bn () Int)
(declare-fun cm () Int)
(declare-fun cn () Int)
(declare-fun dm () Int)
(declare-fun v79prm () node)
(declare-fun res () node)
(declare-fun n () Int)
(declare-fun m () Int)


(assert 
(exists ((xleftprm node)(flted25 Int)(flted26 Int))(and 
;lexvar(= m46 (+ (+ m49 1) m50))
(<= (+ 0 n61) (+ n62 1))
(<= n62 (+ 1 n61))
(= n60 n56)
(<= n53 n54)
(= m37 (+ (+ m41 1) m42))
(<= (+ 0 n51) (+ n52 1))
(<= n52 (+ 1 n51))
(= n50 n45)
(<= aprm Anon15)
(= m (+ (+ m34 1) m35))
(<= (+ 0 n42) (+ n41 1))
(<= n41 (+ 1 n42))
(= n43 n)
(distinct xprm nil)
(= aprm a)
(= xprm x)
(= xleft p11)
(= m36 m35)
(= n44 n41)
(<= 0 m35)
(<= 0 n41)
(= flted19 (+ 1 m36))
(<= 0 m36)
(<= 0 n44)
(= m37 flted19)
(= n45 Anon17)
(<= 0 flted19)
(<= 0 Anon17)
(<= 0 m37)
(<= 0 n45)
(= m38 m34)
(= n46 n42)
(<= 0 m34)
(<= 0 n42)
(= (+ 2 n46) n45)
(= m43 m42)
(= n53 n52)
(<= 0 m42)
(<= 0 n52)
(= m44 m41)
(= n54 n51)
(<= 0 m41)
(<= 0 n51)
(= m45 m43)
(= n55 n53)
(<= 0 m43)
(<= 0 n53)
(= m46 m44)
(= n56 n54)
(<= 0 m44)
(<= 0 n54)
(<= 0 m46)
(<= 0 n56)
(= (+ n55 1) n56)
(= am m45)
(= an n55)
(= bm m50)
(= bn n62)
(= cm m49)
(= cn n61)
(= dm m38)
(<= 0 m38)
(<= 0 n46)
(<= 0 m49)
(<= 0 n61)
(<= 0 m50)
(<= 0 n62)
(<= 0 m45)
(<= 0 n55)
(= flted26 (+ (+ (+ (+ dm bm) 3) am) cm))
(= flted25 (+ 2 an))
(<= 0 am)
(<= 0 an)
(<= 0 bm)
(<= 0 bn)
(<= 0 cm)
(<= 0 cn)
(<= 0 dm)
(= res v79prm)
(tobool (ssep 
(pto q13 (sref (ref val Anon21) (ref height n60) (ref left p15) (ref right q15) ))
(avl v79prm flted26 flted25)
(pto xleftprm (sref (ref val Anon_3699) (ref height n50) (ref left p13) (ref right q13) ))
(pto xprm (sref (ref val Anon15) (ref height n43) (ref left xleftprm) (ref right q11) ))
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