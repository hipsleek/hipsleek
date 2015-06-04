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

























































































(declare-fun xnext_2668 () node)
(declare-fun d5 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun a1 () Int)
(declare-fun sm16 () Int)
(declare-fun bg8 () Int)
(declare-fun flted24 () Int)
(declare-fun aprm () Int)
(declare-fun n9_2667 () Int)
(declare-fun n6 () Int)
(declare-fun sm17_2669 () Int)
(declare-fun sm17 () Int)
(declare-fun bg9_2670 () Int)
(declare-fun bg9 () Int)
(declare-fun res () node)
(declare-fun bg () Int)
(declare-fun sm () Int)
(declare-fun a () Int)
(declare-fun n () Int)


(assert 
(exists ((n9 Int)(xnextprm node))(and 
;lexvar(= (+ flted24 1) n)
(<= sm d5)
(<= d5 bg)
(= sm16 sm)
(= bg8 bg)
(distinct a1 1)
(< a n)
(< 0 a)
(= a1 a)
(= xprm x)
(= (+ aprm 1) a1)
(= n6 flted24)
(= sm17 sm16)
(= bg9 bg8)
(<= 0 flted24)
(= n6 (+ n9 aprm))
(< 0 aprm)
(< 0 n9)
(<= 0 n6)
(tobool (ssep 
(bnd res n9 sm17 bg9)
(bnd xnextprm aprm sm17 bg9)
(pto xprm (sref (ref val d5) (ref next xnextprm) ))
) )
))
)

(assert (not 
(exists ((sm18 Int)(bg10 Int)(sm19 Int)(bg11 Int)(n7 Int)(n8 Int))(and 
(= bg11 bg)
(= sm19 sm)
(= bg10 bg)
(= sm18 sm)
(= n8 a)
(< 0 n7)
(< 0 n8)
(= n (+ n7 n8))
(<= 0 n)
(tobool (ssep 
(bnd xprm n8 sm18 bg10)
(bnd res n7 sm19 bg11)
) )
))
))

(check-sat)