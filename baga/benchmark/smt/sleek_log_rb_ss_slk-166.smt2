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





































































































































































































































































































































































(declare-fun v45 () Int)
(declare-fun r33 () node)
(declare-fun Anon24 () Int)
(declare-fun v50_21267 () node)
(declare-fun cl9_21266 () Int)
(declare-fun flted275_21265 () Int)
(declare-fun bh8 () Int)
(declare-fun cl8 () Int)
(declare-fun Anon23 () Int)
(declare-fun n10 () Int)
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
(exists ((flted275 Int)(cl9 Int)(v50 node))(and 
;lexvar(<= cl8 1)
(<= 0 cl8)
(<= 1 bh8)
(<= 0 n10)
(<= cl9 1)
(<= 0 cl9)
(= cl8 1)
(= (+ flted275 1) n10)
(<= Anon23 1)
(<= 0 Anon23)
(<= 1 bhl33)
(<= 0 nl33)
(= bh8 bhl33)
(= cl8 Anon23)
(= n10 nl33)
(= flted266 0)
(= cl 0)
(= n (+ (+ nr33 1) nl33))
(= bhl33 bhr33)
(= bh (+ bhl33 1))
(= xprm x)
(distinct x nil)
(<= 0 cl)
(<= cl 1)
(distinct l33 nil)
(tobool (ssep 
(pto xprm (sref (ref val v45) (ref color flted266) (ref left l33) (ref right r33) ))
(rb r33 nr33 Anon24 bhr33)
(rb v50 flted275 cl9 bh8)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val33prm) (ref color color34prm) (ref left left33prm) (ref right right33prm) ))
 )
)
))

(check-sat)