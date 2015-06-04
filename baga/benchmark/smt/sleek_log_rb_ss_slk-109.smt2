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
(declare-fun l23 () node)
(declare-fun r23 () node)
(declare-fun v37 () Int)
(declare-fun l25 () node)
(declare-fun r25 () node)
(declare-fun tmpprm () node)
(declare-fun flted223 () Int)
(declare-fun bh4 () Int)
(declare-fun cl4 () Int)
(declare-fun Anon15 () Int)
(declare-fun n4 () Int)
(declare-fun flted215 () Int)
(declare-fun flted214 () Int)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun flted216 () Int)
(declare-fun bhr23 () Int)
(declare-fun nr23 () Int)
(declare-fun flted213 () Int)
(declare-fun flted212 () Int)
(declare-fun nl23 () Int)
(declare-fun bhl23 () Int)
(declare-fun Anon14 () Int)
(declare-fun flted217 () Int)
(declare-fun nr25 () Int)
(declare-fun bhr25 () Int)
(declare-fun flted221 () Int)
(declare-fun nl25 () Int)
(declare-fun bhl25 () Int)
(declare-fun flted222 () Int)
(declare-fun n () Int)
(declare-fun bh () Int)
(declare-fun cl () Int)
(declare-fun flted228_15845 () Int)
(declare-fun flted229_15846 () Int)
(declare-fun flted230_15847 () Int)
(declare-fun na9 () Int)
(declare-fun h22 () Int)
(declare-fun nb9 () Int)
(declare-fun nc9 () Int)
(declare-fun nd () Int)
(declare-fun h () Int)
(declare-fun nc () Int)
(declare-fun nb () Int)


(assert 
(exists ((flted228 Int)(flted229 Int)(flted230 Int))(and 
;lexvar(= flted223 1)
(= flted222 0)
(= flted221 0)
(= n4 (+ (+ nr25 1) nl25))
(= bhl25 bh4)
(= bhr25 bh4)
(<= cl4 1)
(<= 0 cl4)
(<= 1 bh4)
(<= 0 n4)
(= cl4 1)
(<= Anon15 1)
(<= 0 Anon15)
(<= 1 bhr23)
(<= 0 nr23)
(= bh4 bhr23)
(= cl4 Anon15)
(= n4 nr23)
(distinct b nil)
(= flted217 0)
(= flted216 (+ 1 h))
(= flted215 (+ 1 h))
(= flted214 0)
(= cprm c)
(= bprm b)
(= aprm a)
(= flted216 (+ bhl23 1))
(= bhl23 bhr23)
(= nb (+ (+ nr23 1) nl23))
(= flted213 0)
(= flted212 0)
(= n nl23)
(= cl Anon14)
(= bh bhl23)
(<= 0 nl23)
(<= 1 bhl23)
(<= 0 Anon14)
(<= Anon14 1)
(= cl 0)
(= na9 n)
(= h22 bh)
(= nb9 nl25)
(= nc9 nr25)
(= nd nc)
(<= 0 nc)
(<= 1 h)
(<= 0 flted217)
(<= flted217 1)
(<= 0 nr25)
(<= 1 bhr25)
(<= 0 flted221)
(<= flted221 1)
(<= 0 nl25)
(<= 1 bhl25)
(<= 0 flted222)
(<= flted222 1)
(<= 0 n)
(<= 1 bh)
(<= 0 cl)
(<= cl 1)
(= flted228 (+ (+ (+ (+ 3 nc9) na9) nb9) nd))
(= flted229 1)
(= flted230 (+ 1 h22))
(tobool (ssep 
(rb a na flted214 flted215)
(pto bprm (sref (ref val v35) (ref color flted212) (ref left l23) (ref right r23) ))
(pto r23 (sref (ref val v37) (ref color flted223) (ref left l25) (ref right r25) ))
(rb tmpprm flted228 flted229 flted230)
) )
))
)

(assert (not 
(exists ((flted227 Int))(and 
(= h ha)
(= flted227 (+ (+ 1 nb) nc))
(tobool  
(rb tmpprm flted227 Anon16 ha)
 )
))
))

(check-sat)