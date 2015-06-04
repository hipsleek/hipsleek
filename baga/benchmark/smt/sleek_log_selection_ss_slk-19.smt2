(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun sll ((?in node) (?n Int) (?sm Int) (?lg Int))
Space (tospace
(or
(exists ((?sm_26 Int)(?flted_12_24 node))(and 
(= ?flted_12_24 nil)
(= ?sm ?lg)
(= ?n 1)
(= ?sm_26 ?sm)
(tobool  
(pto ?in (sref (ref val ?sm_26) (ref next ?flted_12_24) ))
 )
))(exists ((?sm_27 Int)(?lg_28 Int)(?flted_13_25 Int))(and 
(= (+ ?flted_13_25 1) ?n)
(distinct ?q nil)
(<= ?sm ?qs)
(= ?sm_27 ?sm)
(= ?lg_28 ?lg)
(tobool (ssep 
(pto ?in (sref (ref val ?sm_27) (ref next ?q) ))
(sll ?q ?flted_13_25 ?qs ?lg_28)
) )
)))))

(define-fun bnd1 ((?in node) (?n Int) (?sm NUM) (?bg Int) (?mi NUM))
Space (tospace
(or
(exists ((?mi_33 Int)(?flted_8_31 node))(and 
(= ?flted_8_31 nil)
(<= ?sm ?mi)
(< ?mi ?bg)
(= ?n 1)
(= ?mi_33 ?mi)
(tobool  
(pto ?in (sref (ref val ?mi_33) (ref next ?flted_8_31) ))
 )
))(exists ((?sm_34 Int)(?bg_35 Int)(?flted_9_32 Int))(and 
(= (+ ?flted_9_32 1) ?n)
(<= ?sm ?d)
(< ?d ?bg)
;eqmin(<= ?sm ?mi)
(< ?mi ?bg)
(= ?sm_34 ?sm)
(= ?bg_35 ?bg)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref next ?p) ))
(bnd1 ?p ?flted_9_32 ?sm_34 ?bg_35 ?tmi)
) )
)))))




















































(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun d1 () Int)
(declare-fun flted3 () Int)
(declare-fun sm2 () Int)
(declare-fun tmi1 () Int)
(declare-fun bg2 () Int)
(declare-fun xnext_712 () node)
(declare-fun n1 () Int)
(declare-fun s1 () Int)
(declare-fun mi3 () Int)
(declare-fun l1 () Int)
(declare-fun p1 () node)
(declare-fun l () Int)
(declare-fun s () Int)
(declare-fun mi () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun n () Int)


(assert 
(exists ((xnextprm node))(and 
;lexvar(distinct d1 aprm)
(= a mi)
(<= 1 n)
(= aprm a)
(= xprm x)
(= bg2 l)
(= sm2 s)
(< mi l)
(<= s mi)
;eqmin(< d1 l)
(<= s d1)
(= (+ flted3 1) n)
(= n1 flted3)
(= s1 sm2)
(= l1 bg2)
(= mi3 tmi1)
(<= 1 flted3)
(<= sm2 tmi1)
(< tmi1 bg2)
(= xnextprm nil)
(= n1 1)
(<= 1 n1)
(<= s1 mi3)
(< mi3 l1)
(distinct p1 nil)
(tobool  
(pto xprm (sref (ref val d1) (ref next xnextprm) ))
 )
))
)

(assert (not 
(and 
(< mi l)
(<= s mi)
(= n 1)
(= xprm nil)
(distinct x nil)
(<= 1 n)

)
))

(check-sat)