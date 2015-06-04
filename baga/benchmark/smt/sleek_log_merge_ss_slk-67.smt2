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

























































































(declare-fun bg9 () NUM)
(declare-fun sm17 () NUM)
(declare-fun n6 () Int)
(declare-fun xnextprm () __Exc)
(declare-fun p5 () __Exc)
(declare-fun Anonprm () NUM)
(declare-fun aprm () Int)
(declare-fun xprm () __Exc)
(declare-fun x () __Exc)
(declare-fun a () Int)
(declare-fun a1 () Int)
(declare-fun bg8 () NUM)
(declare-fun sm16 () NUM)
(declare-fun bg () NUM)
(declare-fun sm () NUM)
(declare-fun d5 () NUM)
(declare-fun flted24 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= bg9 bg8)
(= sm17 sm16)
(= n6 flted24)
(= xnextprm p5)
(= Anonprm d5)
(= (+ aprm 1) a1)
(= xprm x)
(= a1 a)
(< 0 a)
(< a n)
(distinct a1 1)
(= bg8 bg)
(= sm16 sm)
(<= d5 bg)
(<= sm d5)
(= (+ flted24 1) n)

)
)

(assert (not 
;lexvar
))

(check-sat)