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





































































































































































































































































































































































(declare-fun nc1 () __Exc)
(declare-fun nd () __Exc)
(declare-fun nb1 () __Exc)
(declare-fun nc () __Exc)
(declare-fun a () __Exc)
(declare-fun b () __Exc)
(declare-fun cprm () __Exc)
(declare-fun c () __Exc)
(declare-fun dprm () __Exc)
(declare-fun d () __Exc)
(declare-fun flted10 () Int)
(declare-fun flted11 () Int)
(declare-fun flted12 () Int)
(declare-fun flted13 () Int)
(declare-fun v () Int)
(declare-fun v1 () Int)
(declare-fun v2 () Int)
(declare-fun l () __Exc)
(declare-fun aprm () __Exc)
(declare-fun r () __Exc)
(declare-fun bprm () __Exc)
(declare-fun na () Int)
(declare-fun nb () Int)
(declare-fun bha () __Exc)
(declare-fun bhr () __Exc)
(declare-fun bhl () __Exc)
(declare-fun bha1 () __Exc)
(declare-fun na1 () Int)
(declare-fun nl () Int)
(declare-fun nr () Int)


(assert 
(and 
;lexvar(= nc1 nd)
(= nb1 nc)
(= aprm a)
(= bprm b)
(= cprm c)
(= dprm d)
(= flted10 0)
(= flted11 0)
(= flted12 0)
(= flted13 0)
(= v2 0)
(= v 1)
(= v1 v2)
(= l aprm)
(= r bprm)
(= nl na)
(= bhl bha)
(= nr nb)
(= bhr bha)
(= bhr bhl)
(= bhr bha1)
(= bhl bha1)
(= na1 (+ (+ nr 1) nl))

)
)

(assert (not 
;lexvar
))

(check-sat)