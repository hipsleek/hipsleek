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
(declare-fun Anon11 () Int)
(declare-fun nb7 () __Exc)
(declare-fun nc () __Exc)
(declare-fun a () __Exc)
(declare-fun b () __Exc)
(declare-fun cprm () __Exc)
(declare-fun c () __Exc)
(declare-fun dprm () __Exc)
(declare-fun d () __Exc)
(declare-fun colorprm () Int)
(declare-fun flted190 () Int)
(declare-fun flted191 () Int)
(declare-fun flted192 () Int)
(declare-fun flted193 () Int)
(declare-fun color () Int)
(declare-fun v31 () Int)
(declare-fun v32 () Int)
(declare-fun v33 () Int)
(declare-fun l21 () __Exc)
(declare-fun aprm () __Exc)
(declare-fun r21 () __Exc)
(declare-fun bprm () __Exc)
(declare-fun na () Int)
(declare-fun nb () Int)
(declare-fun h () __Exc)
(declare-fun bhr21 () __Exc)
(declare-fun bhl21 () __Exc)
(declare-fun ha () __Exc)
(declare-fun na7 () Int)
(declare-fun nl21 () Int)
(declare-fun nr21 () Int)


(assert 
(and 
;lexvar(= nc7 nd)
(= Anon11 flted192)
(= nb7 nc)
(= aprm a)
(= bprm b)
(= cprm c)
(= dprm d)
(= colorprm color)
(= flted190 0)
(= flted191 0)
(= flted192 0)
(= flted193 0)
(= color 1)
(= v33 0)
(= v31 1)
(= v32 v33)
(= l21 aprm)
(= r21 bprm)
(= nl21 na)
(= bhl21 h)
(= nr21 nb)
(= bhr21 h)
(= bhr21 bhl21)
(= bhr21 ha)
(= bhl21 ha)
(= na7 (+ (+ nr21 1) nl21))

)
)

(assert (not 
;lexvar
))

(check-sat)