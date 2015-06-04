(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


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
(declare-fun l23 () node)
(declare-fun r23 () node)
(declare-fun tmpprm () node)
(declare-fun Anon14 () Int)
(declare-fun flted212 () Int)
(declare-fun flted213 () Int)
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
(declare-fun b () node)
(declare-fun nc () Int)
(declare-fun flted217 () Int)
(declare-fun nr23 () Int)
(declare-fun bhr23 () Int)
(declare-fun Anon15 () Int)
(declare-fun n () Int)
(declare-fun bh () Int)
(declare-fun cl () Int)
(declare-fun flted231_16617 () Int)
(declare-fun flted232_16618 () Int)
(declare-fun flted233_16619 () Int)
(declare-fun Anon10 () Int)
(declare-fun na10 () Int)
(declare-fun ha () Int)
(declare-fun nb10 () Int)
(declare-fun Anon11 () Int)
(declare-fun nc10 () Int)
(declare-fun nb () Int)
(declare-fun h () Int)


(assert 
(exists ((flted231 Int)(flted232 Int)(flted233 Int))(and 
;lexvar(= cl 1)
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
(= na10 n)
(= ha bh)
(= nb10 nr23)
(= Anon11 Anon15)
(= nc10 nc)
(<= 0 nc)
(<= 1 h)
(<= 0 flted217)
(<= flted217 1)
(<= 0 nr23)
(<= 1 bhr23)
(<= 0 Anon15)
(<= Anon15 1)
(<= 0 n)
(<= 1 bh)
(<= 0 cl)
(<= cl 1)
(= flted231 (+ (+ (+ 2 nb10) na10) nc10))
(= flted232 1)
(= flted233 (+ 1 ha))
(tobool (ssep 
(rb a na flted214 flted215)
(pto bprm (sref (ref val v35) (ref color flted212) (ref left l23) (ref right r23) ))
(rb tmpprm flted231 flted232 flted233)
) )
))
)

(assert (not 
(exists ((flted234 Int))(and 
(= n5 nb)
(= hb h)
(= flted234 0)
(tobool  
(rb aprm n5 flted234 hb)
 )
))
))

(check-sat)