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





































































































































































































































































































































































(declare-fun nb2 () __Exc)
(declare-fun nb () __Exc)
(declare-fun bha4 () __Exc)
(declare-fun na2 () __Exc)
(declare-fun na () __Exc)
(declare-fun aprm () __Exc)
(declare-fun a () __Exc)
(declare-fun bprm () __Exc)
(declare-fun b () __Exc)
(declare-fun c () __Exc)
(declare-fun d () __Exc)
(declare-fun flted30 () Int)
(declare-fun flted31 () Int)
(declare-fun flted32 () Int)
(declare-fun flted33 () Int)
(declare-fun v3 () Int)
(declare-fun v4 () Int)
(declare-fun v5 () Int)
(declare-fun l1 () __Exc)
(declare-fun cprm () __Exc)
(declare-fun r1 () __Exc)
(declare-fun dprm () __Exc)
(declare-fun nc () Int)
(declare-fun nd () Int)
(declare-fun bha () __Exc)
(declare-fun bhr1 () __Exc)
(declare-fun bhl1 () __Exc)
(declare-fun nc2 () Int)
(declare-fun nl1 () Int)
(declare-fun nr1 () Int)


(assert 
(and 
;lexvar(= nb2 nb)
(= bha4 bha)
(= na2 na)
(= aprm a)
(= bprm b)
(= cprm c)
(= dprm d)
(= flted30 0)
(= flted31 0)
(= flted32 0)
(= flted33 0)
(= v5 0)
(= v3 1)
(= v4 v5)
(= l1 cprm)
(= r1 dprm)
(= nl1 nc)
(= bhl1 bha)
(= nr1 nd)
(= bhr1 bha)
(= nc2 (+ (+ nr1 1) nl1))

)
)

(assert (not 
;lexvar
))

(check-sat)