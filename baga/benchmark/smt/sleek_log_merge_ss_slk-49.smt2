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

























































































(declare-fun x1prm () node)
(declare-fun b2 () Int)
(declare-fun n2 () Int)
(declare-fun s2 () Int)
(declare-fun x2prm () node)
(declare-fun x2 () node)
(declare-fun n1 () Int)
(declare-fun s1 () NUM)
(declare-fun b1 () NUM)
(declare-fun flted15 () Int)
(declare-fun sres5 () Int)
(declare-fun lres5 () Int)
(declare-fun sm11 () Int)
(declare-fun n () Int)
(declare-fun xs () Int)
(declare-fun xl () Int)
(declare-fun x1 () node)
(declare-fun flted11 () node)
(declare-fun v18prm () node)


(assert 
(and 
;lexvar(= flted11 nil)
(= s2 b2)
(= n2 1)
(= sm11 s2)
(distinct x2prm nil)
(= x2prm x2)
(= x1 x1)
(= n n1)
(= xs s1)
(= xl b1)
(<= 1 n1)
(<= s1 b1)
(distinct x1 nil)
(= flted15 (+ 1 n))
;eqmin;eqmax(<= 1 n)
(<= xs xl)
(distinct x1 nil)
(= v18prm flted11)
(= v18prm nil)
(tobool (ssep 
(sll x1prm flted15 sres5 lres5)
(pto x2prm (sref (ref val sm11) (ref next flted11) ))
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