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




















































(declare-fun tmp_2316 () node)
(declare-fun mi11 () NUM)
(declare-fun n5 () Int)
(declare-fun mi10 () Int)
(declare-fun l () Int)
(declare-fun s () Int)
(declare-fun n4 () Int)
(declare-fun flted11 () Int)
(declare-fun s5 () NUM)
(declare-fun mi13 () NUM)
(declare-fun l5 () NUM)
(declare-fun l7_2318 () Int)
(declare-fun n6 () Int)
(declare-fun sm5 () NUM)
(declare-fun mi14 () Int)
(declare-fun lg1 () Int)
(declare-fun x3_2317 () node)
(declare-fun v11prm () node)
(declare-fun res () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun lg () Int)
(declare-fun sm () NUM)
(declare-fun mi () NUM)
(declare-fun n () Int)


(assert 
(exists ((tmpprm node)(x3 Int)(l7 Int))(and 
;lexvar(distinct x nil)
(< mi11 l5)
(<= s5 mi11)
(<= 1 n5)
(< 1 n5)
(<= mi11 mi13)
(= (+ flted11 1) n5)
(< mi10 l)
(<= s mi10)
(<= 1 n4)
(= mi11 mi10)
(= l5 l)
(= s5 s)
(= n5 n4)
(< mi lg)
(<= sm mi)
(<= 1 n)
(= mi10 mi)
(= l lg)
(= s sm)
(= n4 n)
(= n6 flted11)
(= sm5 s5)
(= lg1 l5)
(= mi14 mi13)
(<= 1 flted11)
(<= s5 mi13)
(< mi13 l5)
(< l7 lg1)
(= xprm nil)
(<= 1 n6)
(<= sm5 mi14)
(< mi14 lg1)
(distinct x3 nil)
(= res v11prm)
(tobool (ssep 
(sll tmpprm n6 mi14 l7)
(pto v11prm (sref (ref val mi10) (ref next tmpprm) ))
) )
))
)

(assert (not 
(exists ((n7 Int)(mi15 Int)(l6 Int))(and 
(= mi15 mi)
(= n7 n)
(= xprm nil)
(< l6 lg)
(distinct x nil)
(< mi lg)
(<= sm mi)
(<= 1 n)
(tobool  
(sll res n7 mi15 l6)
 )
))
))

(check-sat)