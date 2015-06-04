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
(declare-fun l45 () node)
(declare-fun v106 () Int)
(declare-fun l49 () node)
(declare-fun v151prm () node)
(declare-fun r49 () node)
(declare-fun flted360 () Int)
(declare-fun flted358 () Int)
(declare-fun nr49 () Int)
(declare-fun bhr49 () Int)
(declare-fun bh47 () Int)
(declare-fun cl () Int)
(declare-fun Anon43 () Int)
(declare-fun n21 () Int)
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
(declare-fun nl49 () Int)
(declare-fun bhl49 () Int)
(declare-fun flted359 () Int)
(declare-fun n22 () Int)
(declare-fun bh48 () Int)
(declare-fun cl26 () Int)


(assert 
(and 
;lexvar(= v151prm r49)
(= flted360 1)
(= flted359 0)
(= flted358 0)
(= n21 (+ (+ nr49 1) nl49))
(= bhl49 bh47)
(= bhr49 bh47)
(<= cl 1)
(<= 0 cl)
(<= 1 bh47)
(<= 0 n21)
(= cl 1)
(<= Anon43 1)
(<= 0 Anon43)
(<= 1 bh46)
(<= 0 flted354)
(= bh47 bh46)
(= cl Anon43)
(= n21 flted354)
(= right1 r45)
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
(= n22 nl49)
(= cl26 flted359)
(= bh48 bhl49)
(<= 0 nl49)
(<= 1 bhl49)
(<= 0 flted359)
(<= flted359 1)
(= cl26 0)
(<= 0 n22)
(<= 1 bh48)
(<= 0 cl26)
(<= cl26 1)
(tobool (ssep 
(rb l45 nl45 Anon32 bhl45)
(pto xprm (sref (ref val v94) (ref color flted340) (ref left l45) (ref right v104) ))
(pto v104 (sref (ref val v106) (ref color flted360) (ref left l49) (ref right r49) ))
(rb r49 nr49 flted358 bhr49)
(rb l49 n22 cl26 bh48)
) )
)
)

(assert (not 
(and 
(tobool  
(rb v151prm n23 cl27 bh49)
 )
)
))

(check-sat)