(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun color () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun rb ((?in node) (?n Int) (?cl Int) (?bh Int))
Space (tospace
(or
(or
(and 
(= ?in nil)
(= ?n 0)
(= ?bh 1)
(= ?cl 0)

)(exists ((?flted_12_38 Int)(?flted_12_39 Int)(?flted_12_40 Int))(and 
(= ?flted_12_40 1)
(= ?flted_12_39 0)
(= ?flted_12_38 0)
(= ?cl 1)
(= ?n (+ (+ ?nr 1) ?nl))
(= ?bhl ?bh)
(= ?bhr ?bh)
(tobool (ssep 
(pto ?in (sref (ref val ?v) (ref color ?flted_12_40) (ref left ?l) (ref right ?r) ))
(rb ?l ?nl ?flted_12_39 ?bhl)
(rb ?r ?nr ?flted_12_38 ?bhr)
) )
)))(exists ((?flted_13_41 Int))(and 
(= ?flted_13_41 0)
(= ?cl 0)
(= ?n (+ (+ ?nr 1) ?nl))
(= ?bhl ?bhr)
(= ?bh (+ ?bhl 1))
(tobool (ssep 
(pto ?in (sref (ref val ?v) (ref color ?flted_13_41) (ref left ?l) (ref right ?r) ))
(rb ?l ?nl ?Anon_14 ?bhl)
(rb ?r ?nr ?Anon_15 ?bhr)
) )
)))))





































































































































































































































































































































































(declare-fun Anon28 () Int)
(declare-fun l39 () node)
(declare-fun v61 () Int)
(declare-fun l41 () node)
(declare-fun r41 () node)
(declare-fun color6 () Int)
(declare-fun v62_23786 () Int)
(declare-fun r39 () node)
(declare-fun flted293 () Int)
(declare-fun n () Int)
(declare-fun nr39 () Int)
(declare-fun bhr39 () Int)
(declare-fun bh () Int)
(declare-fun cl () Int)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun aprm () Int)
(declare-fun v59 () Int)
(declare-fun nl39 () Int)
(declare-fun bhl39 () Int)
(declare-fun Anon27 () Int)
(declare-fun cl12 () Int)
(declare-fun bhr41 () Int)
(declare-fun bhl41 () Int)
(declare-fun bh15 () Int)
(declare-fun n11 () Int)
(declare-fun nl41 () Int)
(declare-fun nr41 () Int)
(declare-fun flted297 () Int)
(declare-fun flted298 () Int)
(declare-fun flted299 () Int)


(assert 
(exists ((v62 Int))(and 
;lexvar(= color6 flted299)
(= v62 0)
(= r39 nil)
(= flted293 0)
(= cl 0)
(= n (+ (+ nr39 1) nl39))
(= bhl39 bhr39)
(= bh (+ bhl39 1))
(distinct xprm nil)
(<= cl 1)
(<= 0 cl)
(= aprm a)
(= xprm x)
(= aprm v59)
(= n11 nl39)
(= cl12 Anon27)
(= bh15 bhl39)
(<= 0 nl39)
(<= 1 bhl39)
(<= 0 Anon27)
(<= Anon27 1)
(= cl12 1)
(<= 0 n11)
(<= 1 bh15)
(<= 0 cl12)
(<= cl12 1)
(= bhr41 bh15)
(= bhl41 bh15)
(= n11 (+ (+ nr41 1) nl41))
(= flted297 0)
(= flted298 0)
(= flted299 1)
(tobool (ssep 
(rb r39 nr39 Anon28 bhr39)
(rb l41 nl41 flted298 bhl41)
(rb r41 nr41 flted297 bhr41)
(pto xprm (sref (ref val v59) (ref color flted293) (ref left l39) (ref right r39) ))
(pto l39 (sref (ref val v61) (ref color v62) (ref left l41) (ref right r41) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val39prm) (ref color color40prm) (ref left left39prm) (ref right right39prm) ))
 )
)
))

(check-sat)