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





































































































































































































































































































































































(declare-fun nc7 () __Exc)
(declare-fun nd () __Exc)
(declare-fun Anon10 () Int)
(declare-fun nb7 () __Exc)
(declare-fun nc () __Exc)
(declare-fun a () __Exc)
(declare-fun b () __Exc)
(declare-fun cprm () __Exc)
(declare-fun c () __Exc)
(declare-fun dprm () __Exc)
(declare-fun d () __Exc)
(declare-fun colorprm () Int)
(declare-fun flted182 () Int)
(declare-fun flted183 () Int)
(declare-fun flted184 () Int)
(declare-fun flted185 () Int)
(declare-fun color () Int)
(declare-fun v28 () Int)
(declare-fun v29 () Int)
(declare-fun v30 () Int)
(declare-fun l20 () __Exc)
(declare-fun aprm () __Exc)
(declare-fun r20 () __Exc)
(declare-fun bprm () __Exc)
(declare-fun na () Int)
(declare-fun nb () Int)
(declare-fun h () __Exc)
(declare-fun bhr20 () __Exc)
(declare-fun bhl20 () __Exc)
(declare-fun ha () __Exc)
(declare-fun na7 () Int)
(declare-fun nl20 () Int)
(declare-fun nr20 () Int)


(assert 
(and 
;lexvar(= nc7 nd)
(= Anon10 flted184)
(= nb7 nc)
(= aprm a)
(= bprm b)
(= cprm c)
(= dprm d)
(= colorprm color)
(= flted182 0)
(= flted183 0)
(= flted184 0)
(= flted185 0)
(= color 0)
(= v30 0)
(= v28 1)
(= v29 v30)
(= l20 aprm)
(= r20 bprm)
(= nl20 na)
(= bhl20 h)
(= nr20 nb)
(= bhr20 h)
(= bhr20 bhl20)
(= bhr20 ha)
(= bhl20 ha)
(= na7 (+ (+ nr20 1) nl20))

)
)

(assert (not 
;lexvar
))

(check-sat)