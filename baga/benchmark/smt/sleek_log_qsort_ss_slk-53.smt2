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
(exists ((?flted_13_23 node))(and 
(= ?flted_13_23 nil)
(= ?qmin ?sm)
(= ?qmin ?lg)
(= ?n 1)
(tobool  
(pto ?in (sref (ref val ?qmin) (ref next ?flted_13_23) ))
 )
))(exists ((?sm_25 Int)(?lg_26 Int)(?flted_14_24 Int))(and 
(= (+ ?flted_14_24 1) ?n)
(<= ?sm ?qs)
(= ?sm_25 ?sm)
(= ?lg_26 ?lg)
(tobool (ssep 
(pto ?in (sref (ref val ?sm_25) (ref next ?q) ))
(sll ?q ?flted_14_24 ?qs ?lg_26)
) )
)))))

(define-fun bnd ((?in node) (?n Int) (?sm Int) (?bg Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?sm_29 Int)(?bg_30 Int)(?flted_9_28 Int))(and 
(= (+ ?flted_9_28 1) ?n)
(<= ?sm ?d)
(< ?d ?bg)
(= ?sm_29 ?sm)
(= ?bg_30 ?bg)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref next ?p) ))
(bnd ?p ?flted_9_28 ?sm_29 ?bg_30)
) )
)))))
























































































(declare-fun tmpprm () node)
(declare-fun sm () Int)
(declare-fun bg () Int)
(declare-fun n () Int)
(declare-fun xsprm () node)
(declare-fun xs () node)
(declare-fun d3 () Int)
(declare-fun sm10 () Int)
(declare-fun sm9 () Int)
(declare-fun bg8 () Int)
(declare-fun bg7 () Int)
(declare-fun flted10 () Int)
(declare-fun a5 () Int)
(declare-fun b10 () Int)
(declare-fun n3 () Int)
(declare-fun xsnext3 () node)
(declare-fun v9prm () node)
(declare-fun v5_1912 () Int)
(declare-fun v5prm () Int)


(assert 
(and 
;lexvar(= (+ flted10 1) n)
(<= sm d3)
(< d3 bg)
(= sm9 sm)
(= bg7 bg)
(distinct xsprm nil)
(< 0 n)
(= xsprm xs)
(= v5prm d3)
(= n3 flted10)
(= sm10 sm9)
(= bg8 bg7)
(<= 0 flted10)
(= n3 (+ b10 a5))
(<= 0 n3)
(= v9prm xsnext3)
(distinct v9prm nil)
(tobool (ssep 
(bnd tmpprm b10 v5prm bg8)
(bnd xsnext3 a5 sm10 v5prm)
(pto xsprm (sref (ref val d3) (ref next xsnext3) ))
) )
)
)

(assert (not 
;lexvar
))

(check-sat)