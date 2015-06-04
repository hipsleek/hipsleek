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
(declare-fun v46_20622 () Int)
(declare-fun l34_20623 () node)
(declare-fun r34_20626 () node)
(declare-fun v105prm () node)
(declare-fun r33 () node)
(declare-fun v103prm () Int)
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
(declare-fun bhr34_20628 () Int)
(declare-fun bhl34_20625 () Int)
(declare-fun bh7 () Int)
(declare-fun n9 () Int)
(declare-fun nl34_20624 () Int)
(declare-fun nr34_20627 () Int)
(declare-fun flted267_20619 () Int)
(declare-fun flted268_20620 () Int)
(declare-fun flted269_20621 () Int)


(assert 
(exists ((flted267 Int)(flted268 Int)(flted269 Int)(v46 Int)(l34 node)(nl34 Int)(bhl34 Int)(r34 node)(nr34 Int)(bhr34 Int))(and 
;lexvar(= v105prm r33)
(= v103prm 0)
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
(= bhr34 bh7)
(= bhl34 bh7)
(= n9 (+ (+ nr34 1) nl34))
(= flted267 0)
(= flted268 0)
(= flted269 1)
(tobool (ssep 
(rb l33 nl33 Anon23 bhl33)
(pto v105prm (sref (ref val v46) (ref color flted269) (ref left l34) (ref right r34) ))
(rb l34 nl34 flted268 bhl34)
(rb r34 nr34 flted267 bhr34)
(pto xprm (sref (ref val v45) (ref color flted266) (ref left l33) (ref right r33) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto v105prm (sref (ref val val30prm) (ref color color31prm) (ref left left30prm) (ref right right30prm) ))
 )
)
))

(check-sat)