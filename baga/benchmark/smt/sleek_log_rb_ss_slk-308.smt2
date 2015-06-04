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





































































































































































































































































































































































(declare-fun Anon37 () Int)
(declare-fun r44 () node)
(declare-fun v93 () Int)
(declare-fun flted339 () Int)
(declare-fun Anon29 () Int)
(declare-fun n () Int)
(declare-fun nr44 () Int)
(declare-fun bhr44 () Int)
(declare-fun bh () Int)
(declare-fun tmp1prm () node)
(declare-fun v125prm () Int)
(declare-fun v90 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun tmpprm () node)
(declare-fun nl44 () Int)
(declare-fun bhl44 () Int)
(declare-fun flted338 () Int)
(declare-fun flted343 () Int)
(declare-fun v97 () node)
(declare-fun bh37 () Int)
(declare-fun n16 () Int)
(declare-fun bh34 () Int)
(declare-fun Anon34 () Int)
(declare-fun left () node)
(declare-fun l44 () node)
(declare-fun flted337 () Int)
(declare-fun v130prm () Int)
(declare-fun v131prm () Int)


(assert 
(and 
;lexvar(<= v125prm v93)
(= flted337 1)
(= flted338 0)
(= flted339 0)
(= Anon29 1)
(= n (+ (+ nr44 1) nl44))
(= bhl44 bh)
(= bhr44 bh)
(distinct xprm nil)
(= tmp1prm nil)
(= v125prm v90)
(= xprm x)
(= tmpprm l44)
(= n16 nl44)
(= Anon34 flted338)
(= bh34 bhl44)
(<= 0 nl44)
(<= 1 bhl44)
(<= 0 flted338)
(<= flted338 1)
(= flted343 (+ 1 n16))
(distinct v97 nil)
(<= bh34 bh37)
(<= bh37 bh34)
(<= 0 n16)
(<= 1 bh34)
(<= 0 Anon34)
(<= Anon34 1)
(= left l44)
(= v130prm flted337)
(= v131prm 0)
(distinct v130prm v131prm)
(tobool (ssep 
(rb r44 nr44 flted339 bhr44)
(rb v97 flted343 Anon37 bh37)
(pto xprm (sref (ref val v93) (ref color flted337) (ref left v97) (ref right r44) ))
) )
)
)

(assert (not 
;lexvar
))

(check-sat)