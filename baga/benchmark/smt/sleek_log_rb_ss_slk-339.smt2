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





































































































































































































































































































































































(declare-fun Anon32 () Int)
(declare-fun Anon43 () Int)
(declare-fun l45 () node)
(declare-fun right1 () node)
(declare-fun bh46 () Int)
(declare-fun v104 () node)
(declare-fun flted354 () Int)
(declare-fun bh42 () Int)
(declare-fun Anon39 () Int)
(declare-fun Anon33 () Int)
(declare-fun n20 () Int)
(declare-fun tmpprm () node)
(declare-fun r45 () node)
(declare-fun x () node)
(declare-fun v90 () Int)
(declare-fun tmp1prm () node)
(declare-fun xprm () node)
(declare-fun bh () Int)
(declare-fun bhl45 () Int)
(declare-fun bhr45 () Int)
(declare-fun n () Int)
(declare-fun nl45 () Int)
(declare-fun nr45 () Int)
(declare-fun Anon29 () Int)
(declare-fun flted340 () Int)
(declare-fun v94 () Int)
(declare-fun v125prm () Int)


(assert 
(and 
;lexvar(= right1 r45)
(<= Anon39 1)
(<= 0 Anon39)
(<= 1 bh42)
(<= 0 n20)
(<= bh46 bh42)
(<= bh42 bh46)
(distinct v104 nil)
(= flted354 (+ 1 n20))
(<= Anon33 1)
(<= 0 Anon33)
(<= 1 bhr45)
(<= 0 nr45)
(= bh42 bhr45)
(= Anon39 Anon33)
(= n20 nr45)
(= tmpprm r45)
(= xprm x)
(= v125prm v90)
(= tmp1prm nil)
(distinct xprm nil)
(= bh (+ bhl45 1))
(= bhl45 bhr45)
(= n (+ (+ nr45 1) nl45))
(= Anon29 0)
(= flted340 0)
(< v94 v125prm)
(tobool (ssep 
(rb l45 nl45 Anon32 bhl45)
(rb v104 flted354 Anon43 bh46)
(pto xprm (sref (ref val v94) (ref color flted340) (ref left l45) (ref right v104) ))
) )
)
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val59prm) (ref color color60prm) (ref left left59prm) (ref right right59prm) ))
 )
)
))

(check-sat)