(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun sll ((?in node) (?n Int) (?sm Int) (?lg Int))
Space (tospace
(or
(exists ((?sm_28 Int)(?flted_21_26 node))(and 
(= ?flted_21_26 nil)
(= ?sm ?lg)
(= ?n 1)
(= ?sm_28 ?sm)
(tobool  
(pto ?in (sref (ref val ?sm_28) (ref next ?flted_21_26) ))
 )
))(exists ((?sm_29 Int)(?lg_30 Int)(?flted_22_27 Int))(and 
(= (+ ?flted_22_27 1) ?n)
(<= ?sm ?qs)
(= ?sm_29 ?sm)
(= ?lg_30 ?lg)
(tobool (ssep 
(pto ?in (sref (ref val ?sm_29) (ref next ?q) ))
(sll ?q ?flted_22_27 ?qs ?lg_30)
) )
)))))

(define-fun bnd ((?in node) (?n Int) (?sm Int) (?bg Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?sm_33 Int)(?bg_34 Int)(?flted_9_32 Int))(and 
(= (+ ?flted_9_32 1) ?n)
(<= ?sm ?d)
(<= ?d ?bg)
(= ?sm_33 ?sm)
(= ?bg_34 ?bg)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref next ?p) ))
(bnd ?p ?flted_9_32 ?sm_33 ?bg_34)
) )
)))))

























































































(declare-fun p8 () node)
(declare-fun d8 () NUM)
(declare-fun p7 () node)
(declare-fun bg13 () NUM)
(declare-fun sm21 () NUM)
(declare-fun d7 () NUM)
(declare-fun flted26 () Int)
(declare-fun xs () node)
(declare-fun sm22 () NUM)
(declare-fun bg14 () NUM)
(declare-fun n10 () Int)
(declare-fun n11 () Int)
(declare-fun n14 () Int)
(declare-fun sm24 () NUM)
(declare-fun bg16 () NUM)
(declare-fun sm23 () NUM)
(declare-fun bg15 () NUM)
(declare-fun sm25 () NUM)
(declare-fun bg17 () NUM)
(declare-fun n15 () Int)
(declare-fun bgres3 () NUM)
(declare-fun n12 () Int)
(declare-fun smres1 () NUM)
(declare-fun bgres1 () NUM)
(declare-fun flted27_3604 () Int)
(declare-fun s4_3605 () Int)
(declare-fun b4_3606 () Int)
(declare-fun n1 () Int)
(declare-fun s1 () Int)
(declare-fun b1 () Int)
(declare-fun n2 () Int)
(declare-fun smres3 () Int)
(declare-fun b2 () Int)
(declare-fun s3_3607 () node)
(declare-fun v27prm () node)
(declare-fun res () node)
(declare-fun bg () Int)
(declare-fun sm () NUM)
(declare-fun n () Int)


(assert 
(exists ((flted27 Int)(s4 Int)(b4 Int)(s3prm Int))(and 
;lexvar(= (+ flted26 1) n10)
(<= sm22 d8)
(<= d8 bg14)
(= sm21 sm22)
(= bg13 bg14)
(<= sm21 d8)
(<= d8 bg13)
(= p8 p7)
(= d8 d7)
(distinct p7 nil)
(< 0 n)
(= bg13 bg)
(= sm21 sm)
(<= d7 bg)
(<= sm d7)
(= (+ flted26 1) n)
(<= 0 flted26)
(distinct xs nil)
(= (+ n15 n15) n10)
(= n11 n10)
(= sm23 sm22)
(= bg15 bg14)
(<= 0 n10)
(= n11 (+ n14 n15))
(< 0 n14)
(<= 0 n11)
(= n12 n14)
(= sm24 sm23)
(= bg16 bg15)
(<= 0 n14)
(<= sm24 smres1)
(<= bgres1 bg16)
(<= 0 n12)
(= sm25 sm23)
(= bg17 bg15)
(<= sm25 smres3)
(<= bgres3 bg17)
(<= 0 n15)
(= n1 n12)
(= s1 smres1)
(= b1 bgres1)
(= n2 n15)
(= b2 bgres3)
(<= 1 n15)
(<= smres3 bgres3)
(<= 1 n12)
(<= smres1 bgres1)
(= flted27 (+ n2 n1))
;eqmin;eqmax(<= 1 n1)
(<= s1 b1)
(distinct smres3 nil)
(<= 1 n2)
(<= smres3 b2)
(distinct s3prm nil)
(= res v27prm)
(tobool  
(sll v27prm flted27 s4 b4)
 )
))
)

(assert (not 
(exists ((n16 Int)(smres4 Int)(bgres4 Int))(and 
(= n16 n)
(<= bgres4 bg)
(<= sm smres4)
(<= 0 n)
(tobool  
(sll res n16 smres4 bgres4)
 )
))
))

(check-sat)