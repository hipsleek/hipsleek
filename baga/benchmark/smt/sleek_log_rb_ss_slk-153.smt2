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
(declare-fun bh7 () Int)
(declare-fun cl7 () node)
(declare-fun Anon24 () node)
(declare-fun n9 () Int)
(declare-fun v102prm () node)
(declare-fun r33 () node)
(declare-fun tmpprm () Int)
(declare-fun v45 () Int)
(declare-fun flted266 () Int)
(declare-fun n () Int)
(declare-fun nl33 () Int)
(declare-fun nr33 () Int)
(declare-fun bhr33 () Int)
(declare-fun bh () Int)
(declare-fun bhl33 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun cl () Int)
(declare-fun l33 () node)


(assert 
(and 
;lexvar(= bh7 bhr33)
(= cl7 Anon24)
(= n9 nr33)
(= v102prm r33)
(= tmpprm v45)
(= flted266 0)
(= cl 0)
(= n (+ (+ nr33 1) nl33))
(= bhl33 bhr33)
(= bh (+ bhl33 1))
(= xprm x)
(distinct x nil)
(<= 0 cl)
(<= cl 1)
(= l33 nil)
(tobool (ssep 
(pto xprm (sref (ref val v45) (ref color flted266) (ref left l33) (ref right r33) ))
(rb l33 nl33 Anon23 bhl33)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)