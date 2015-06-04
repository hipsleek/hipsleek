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





































































































































































































































































































































































(declare-fun r44 () node)
(declare-fun Anon35_29619 () Int)
(declare-fun bh35_29620 () Int)
(declare-fun v129prm () node)
(declare-fun flted341_29618 () Int)
(declare-fun bh34 () Int)
(declare-fun Anon34 () Int)
(declare-fun n16 () Int)
(declare-fun tmpprm () node)
(declare-fun l44 () node)
(declare-fun x () node)
(declare-fun v90 () Int)
(declare-fun tmp1prm () node)
(declare-fun xprm () node)
(declare-fun bhr44 () Int)
(declare-fun bhl44 () Int)
(declare-fun bh () Int)
(declare-fun n () Int)
(declare-fun nl44 () Int)
(declare-fun nr44 () Int)
(declare-fun Anon29 () Int)
(declare-fun flted339 () Int)
(declare-fun flted338 () Int)
(declare-fun flted337 () Int)
(declare-fun v125prm () Int)
(declare-fun v93 () Int)


(assert 
(exists ((flted341 Int)(Anon35 Int)(bh35 Int))(and 
;lexvar(<= Anon34 1)
(<= 0 Anon34)
(<= 1 bh34)
(<= 0 n16)
(<= bh35 bh34)
(<= bh34 bh35)
(distinct v129prm nil)
(= flted341 (+ 1 n16))
(<= flted338 1)
(<= 0 flted338)
(<= 1 bhl44)
(<= 0 nl44)
(= bh34 bhl44)
(= Anon34 flted338)
(= n16 nl44)
(= tmpprm l44)
(= xprm x)
(= v125prm v90)
(= tmp1prm nil)
(distinct xprm nil)
(= bhr44 bh)
(= bhl44 bh)
(= n (+ (+ nr44 1) nl44))
(= Anon29 1)
(= flted339 0)
(= flted338 0)
(= flted337 1)
(<= v125prm v93)
(tobool (ssep 
(rb r44 nr44 flted339 bhr44)
(pto xprm (sref (ref val v93) (ref color flted337) (ref left l44) (ref right r44) ))
(rb v129prm flted341 Anon35 bh35)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val49prm) (ref color color50prm) (ref left left49prm) (ref right right49prm) ))
 )
)
))

(check-sat)