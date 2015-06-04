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

























































































(declare-fun next2 () node)
(declare-fun p3 () node)
(declare-fun v23_2560 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun aprm () Int)
(declare-fun bg6 () Int)
(declare-fun sm14 () Int)
(declare-fun d3 () Int)
(declare-fun flted22 () Int)
(declare-fun res () node)
(declare-fun bg () Int)
(declare-fun sm () Int)
(declare-fun a () Int)
(declare-fun n () Int)


(assert 
(exists ((v23prm node))(and 
;lexvar(= res p3)
(= next2 p3)
(= v23prm nil)
(= xprm x)
(= aprm a)
(< 0 a)
(< a n)
(= aprm 1)
(= bg6 bg)
(= sm14 sm)
(<= d3 bg)
(<= sm d3)
(= (+ flted22 1) n)
(tobool (ssep 
(bnd p3 flted22 sm14 bg6)
(pto xprm (sref (ref val d3) (ref next v23prm) ))
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