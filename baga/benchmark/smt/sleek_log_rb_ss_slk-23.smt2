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





































































































































































































































































































































































(declare-fun Anon1 () Int)
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
(declare-fun flted88 () Int)
(declare-fun flted89 () Int)
(declare-fun flted90 () Int)
(declare-fun flted91 () Int)
(declare-fun color () Int)
(declare-fun v13 () Int)
(declare-fun v14 () Int)
(declare-fun v15 () Int)
(declare-fun l7 () __Exc)
(declare-fun cprm () __Exc)
(declare-fun r7 () __Exc)
(declare-fun dprm () __Exc)
(declare-fun nc () Int)
(declare-fun nd () Int)
(declare-fun h () __Exc)
(declare-fun bhr7 () __Exc)
(declare-fun bhl7 () __Exc)
(declare-fun nc3 () Int)
(declare-fun nl7 () Int)
(declare-fun nr7 () Int)


(assert 
(and 
;lexvar(= Anon1 flted89)
(= nb3 nb)
(= h9 h)
(= na3 na)
(= aprm a)
(= bprm b)
(= cprm c)
(= dprm d)
(= colorprm color)
(= flted88 0)
(= flted89 0)
(= flted90 0)
(= flted91 0)
(= color 1)
(= v15 0)
(= v13 1)
(= v14 v15)
(= l7 cprm)
(= r7 dprm)
(= nl7 nc)
(= bhl7 h)
(= nr7 nd)
(= bhr7 h)
(= nc3 (+ (+ nr7 1) nl7))

)
)

(assert (not 
;lexvar
))

(check-sat)