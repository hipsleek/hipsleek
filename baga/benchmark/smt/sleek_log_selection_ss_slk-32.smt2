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




















































(declare-fun mi8 () Int)
(declare-fun l3 () Int)
(declare-fun s3 () Int)
(declare-fun n2 () Int)
(declare-fun v4prm () node)
(declare-fun flted9 () Int)
(declare-fun d3 () Int)
(declare-fun tmi3 () Int)
(declare-fun mi () Int)
(declare-fun sm4 () Int)
(declare-fun s () Int)
(declare-fun bg4 () Int)
(declare-fun l () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun n () Int)
(declare-fun p3 () node)


(assert 
(and 
;lexvar(= mi8 tmi3)
(= l3 bg4)
(= s3 sm4)
(= n2 flted9)
(= v4prm p3)
(= (+ flted9 1) n)
(<= s d3)
(< d3 l)
;eqmin(<= s mi)
(< mi l)
(= sm4 s)
(= bg4 l)
(= xprm x)
(< 0 n)
(distinct p3 nil)
(tobool  
(pto xprm (sref (ref val d3) (ref next p3) ))
 )
)
)

(assert (not 
;lexvar
))

(check-sat)