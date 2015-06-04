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





































































































































































































































































































































































(declare-fun Anon42 () Int)
(declare-fun l44 () node)
(declare-fun v93 () Int)
(declare-fun flted338 () Int)
(declare-fun Anon29 () Int)
(declare-fun n () Int)
(declare-fun nl44 () Int)
(declare-fun bhl44 () Int)
(declare-fun bh () Int)
(declare-fun tmp1prm () node)
(declare-fun v125prm () Int)
(declare-fun v90 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun tmpprm () node)
(declare-fun nr44 () Int)
(declare-fun bhr44 () Int)
(declare-fun flted339 () Int)
(declare-fun flted353 () Int)
(declare-fun v103 () node)
(declare-fun bh45 () Int)
(declare-fun n20 () Int)
(declare-fun bh42 () Int)
(declare-fun Anon39 () Int)
(declare-fun right () node)
(declare-fun r44 () node)
(declare-fun flted337 () Int)
(declare-fun v142prm () Int)
(declare-fun v143prm () Int)


(assert 
(and 
;lexvar(< v93 v125prm)
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
(= tmpprm r44)
(= n20 nr44)
(= Anon39 flted339)
(= bh42 bhr44)
(<= 0 nr44)
(<= 1 bhr44)
(<= 0 flted339)
(<= flted339 1)
(= flted353 (+ 1 n20))
(distinct v103 nil)
(<= bh42 bh45)
(<= bh45 bh42)
(<= 0 n20)
(<= 1 bh42)
(<= 0 Anon39)
(<= Anon39 1)
(= right r44)
(= v142prm flted337)
(= v143prm 0)
(distinct v142prm v143prm)
(tobool (ssep 
(rb l44 nl44 flted338 bhl44)
(rb v103 flted353 Anon42 bh45)
(pto xprm (sref (ref val v93) (ref color flted337) (ref left l44) (ref right v103) ))
) )
)
)

(assert (not 
;lexvar
))

(check-sat)