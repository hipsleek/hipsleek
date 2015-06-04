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





































































































































































































































































































































































(declare-fun na () Int)
(declare-fun v35 () Int)
(declare-fun nc () Int)
(declare-fun v36_14352 () Int)
(declare-fun l24_14353 () node)
(declare-fun r24_14356 () node)
(declare-fun v73prm () node)
(declare-fun r23 () node)
(declare-fun v72prm () node)
(declare-fun l23 () node)
(declare-fun bh () Int)
(declare-fun cl () Int)
(declare-fun Anon14 () Int)
(declare-fun n () Int)
(declare-fun flted212 () Int)
(declare-fun flted213 () Int)
(declare-fun nb () Int)
(declare-fun nl23 () Int)
(declare-fun bhl23 () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun flted214 () Int)
(declare-fun flted215 () Int)
(declare-fun flted216 () Int)
(declare-fun h () Int)
(declare-fun flted217 () Int)
(declare-fun b () node)
(declare-fun nr23 () Int)
(declare-fun bhr23 () Int)
(declare-fun Anon15 () Int)
(declare-fun cl4 () Int)
(declare-fun bhr24_14358 () Int)
(declare-fun bhl24_14355 () Int)
(declare-fun bh4 () Int)
(declare-fun n4 () Int)
(declare-fun nl24_14354 () Int)
(declare-fun nr24_14357 () Int)
(declare-fun flted218_14349 () Int)
(declare-fun flted219_14350 () Int)
(declare-fun flted220_14351 () Int)


(assert 
(exists ((flted218 Int)(flted219 Int)(flted220 Int)(v36 Int)(l24 node)(nl24 Int)(bhl24 Int)(r24 node)(nr24 Int)(bhr24 Int))(and 
;lexvar(= v73prm r23)
(= v72prm l23)
(<= cl 1)
(<= 0 cl)
(<= 1 bh)
(<= 0 n)
(= cl 0)
(<= Anon14 1)
(<= 0 Anon14)
(<= 1 bhl23)
(<= 0 nl23)
(= bh bhl23)
(= cl Anon14)
(= n nl23)
(= flted212 0)
(= flted213 0)
(= nb (+ (+ nr23 1) nl23))
(= bhl23 bhr23)
(= flted216 (+ bhl23 1))
(= aprm a)
(= bprm b)
(= cprm c)
(= flted214 0)
(= flted215 (+ 1 h))
(= flted216 (+ 1 h))
(= flted217 0)
(distinct b nil)
(= n4 nr23)
(= cl4 Anon15)
(= bh4 bhr23)
(<= 0 nr23)
(<= 1 bhr23)
(<= 0 Anon15)
(<= Anon15 1)
(= cl4 1)
(<= 0 n4)
(<= 1 bh4)
(<= 0 cl4)
(<= cl4 1)
(= bhr24 bh4)
(= bhl24 bh4)
(= n4 (+ (+ nr24 1) nl24))
(= flted218 0)
(= flted219 0)
(= flted220 1)
(tobool (ssep 
(rb a na flted214 flted215)
(pto bprm (sref (ref val v35) (ref color flted212) (ref left l23) (ref right r23) ))
(rb c nc flted217 h)
(rb l23 n cl bh)
(pto v73prm (sref (ref val v36) (ref color flted220) (ref left l24) (ref right r24) ))
(rb l24 nl24 flted219 bhl24)
(rb r24 nr24 flted218 bhr24)
) )
))
)

(assert (not 
(and 
(tobool  
(pto v73prm (sref (ref val val20prm) (ref color color21prm) (ref left left20prm) (ref right right20prm) ))
 )
)
))

(check-sat)