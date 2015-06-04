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





































































































































































































































































































































































(declare-fun Anon () Int)
(declare-fun nb3 () __Exc)
(declare-fun nb () __Exc)
(declare-fun h9 () __Exc)
(declare-fun na3 () __Exc)
(declare-fun na () __Exc)
(declare-fun aprm () __Exc)
(declare-fun a () __Exc)
(declare-fun bprm () __Exc)
(declare-fun b () __Exc)
(declare-fun c () __Exc)
(declare-fun d () __Exc)
(declare-fun colorprm () Int)
(declare-fun flted80 () Int)
(declare-fun flted81 () Int)
(declare-fun flted82 () Int)
(declare-fun flted83 () Int)
(declare-fun color () Int)
(declare-fun v10 () Int)
(declare-fun v11 () Int)
(declare-fun v12 () Int)
(declare-fun l6 () __Exc)
(declare-fun cprm () __Exc)
(declare-fun r6 () __Exc)
(declare-fun dprm () __Exc)
(declare-fun nc () Int)
(declare-fun nd () Int)
(declare-fun h () __Exc)
(declare-fun bhr6 () __Exc)
(declare-fun bhl6 () __Exc)
(declare-fun nc3 () Int)
(declare-fun nl6 () Int)
(declare-fun nr6 () Int)


(assert 
(and 
;lexvar(= Anon flted81)
(= nb3 nb)
(= h9 h)
(= na3 na)
(= aprm a)
(= bprm b)
(= cprm c)
(= dprm d)
(= colorprm color)
(= flted80 0)
(= flted81 0)
(= flted82 0)
(= flted83 0)
(= color 0)
(= v12 0)
(= v10 1)
(= v11 v12)
(= l6 cprm)
(= r6 dprm)
(= nl6 nc)
(= bhl6 h)
(= nr6 nd)
(= bhr6 h)
(= nc3 (+ (+ nr6 1) nl6))

)
)

(assert (not 
;lexvar
))

(check-sat)