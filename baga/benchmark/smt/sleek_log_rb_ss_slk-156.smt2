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





































































































































































































































































































































































(declare-fun Anon23 () Int)
(declare-fun r33 () node)
(declare-fun v47 () Int)
(declare-fun l35 () node)
(declare-fun r35 () node)
(declare-fun color5 () Int)
(declare-fun v48_20714 () Int)
(declare-fun l33 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun bh () Int)
(declare-fun bhl33 () Int)
(declare-fun n () Int)
(declare-fun nl33 () Int)
(declare-fun cl () Int)
(declare-fun flted266 () Int)
(declare-fun tmpprm () Int)
(declare-fun v45 () Int)
(declare-fun nr33 () Int)
(declare-fun bhr33 () Int)
(declare-fun Anon24 () Int)
(declare-fun cl7 () Int)
(declare-fun bhr35 () Int)
(declare-fun bhl35 () Int)
(declare-fun bh7 () Int)
(declare-fun n9 () Int)
(declare-fun nl35 () Int)
(declare-fun nr35 () Int)
(declare-fun flted270 () Int)
(declare-fun flted271 () Int)
(declare-fun flted272 () Int)


(assert 
(exists ((v48 Int))(and 
;lexvar(= color5 flted272)
(= v48 0)
(= l33 nil)
(<= cl 1)
(<= 0 cl)
(distinct x nil)
(= xprm x)
(= bh (+ bhl33 1))
(= bhl33 bhr33)
(= n (+ (+ nr33 1) nl33))
(= cl 0)
(= flted266 0)
(= tmpprm v45)
(= n9 nr33)
(= cl7 Anon24)
(= bh7 bhr33)
(<= 0 nr33)
(<= 1 bhr33)
(<= 0 Anon24)
(<= Anon24 1)
(= cl7 1)
(<= 0 n9)
(<= 1 bh7)
(<= 0 cl7)
(<= cl7 1)
(= bhr35 bh7)
(= bhl35 bh7)
(= n9 (+ (+ nr35 1) nl35))
(= flted270 0)
(= flted271 0)
(= flted272 1)
(tobool (ssep 
(rb l33 nl33 Anon23 bhl33)
(rb l35 nl35 flted271 bhl35)
(rb r35 nr35 flted270 bhr35)
(pto xprm (sref (ref val v45) (ref color flted266) (ref left l33) (ref right r33) ))
(pto r33 (sref (ref val v47) (ref color v48) (ref left l35) (ref right r35) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val31prm) (ref color color32prm) (ref left left31prm) (ref right right31prm) ))
 )
)
))

(check-sat)