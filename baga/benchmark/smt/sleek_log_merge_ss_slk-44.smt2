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

























































































(declare-fun xl () node)
(declare-fun b1 () node)
(declare-fun xs () node)
(declare-fun s1 () node)
(declare-fun n () node)
(declare-fun n1 () node)
(declare-fun v17prm () Int)
(declare-fun x1 () node)
(declare-fun x2 () node)
(declare-fun x2prm () node)
(declare-fun x1prm () node)
(declare-fun sm11 () Int)
(declare-fun n2 () Int)
(declare-fun s2 () Int)
(declare-fun b2 () Int)
(declare-fun flted11 () node)


(assert 
(and 
;lexvar(= xl b1)
(= xs s1)
(= n n1)
(= v17prm sm11)
(= x1prm x1)
(= x2prm x2)
(distinct x2prm nil)
(distinct x1prm nil)
(= sm11 s2)
(= n2 1)
(= s2 b2)
(= flted11 nil)
(tobool  
(pto x2prm (sref (ref val sm11) (ref next flted11) ))
 )
)
)

(assert (not 
;lexvar
))

(check-sat)