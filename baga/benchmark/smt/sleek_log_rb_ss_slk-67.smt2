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





































































































































































































































































































































































(declare-fun v21 () Int)
(declare-fun l13 () node)
(declare-fun r13 () node)
(declare-fun tmp_9152 () node)
(declare-fun Anon9 () Int)
(declare-fun flted118 () Int)
(declare-fun flted119 () Int)
(declare-fun nr13 () Int)
(declare-fun bhr13 () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun cprm () node)
(declare-fun flted121 () Int)
(declare-fun flted122 () Int)
(declare-fun flted123 () Int)
(declare-fun b () node)
(declare-fun c () node)
(declare-fun n () Int)
(declare-fun bh () Int)
(declare-fun cl () Int)
(declare-fun nl13 () Int)
(declare-fun bhl13 () Int)
(declare-fun Anon8 () Int)
(declare-fun flted120 () Int)
(declare-fun flted139_9147 () Int)
(declare-fun flted140_9148 () Int)
(declare-fun flted141_9149 () Int)
(declare-fun Anon () Int)
(declare-fun na6 () Int)
(declare-fun h21 () Int)
(declare-fun nb6 () Int)
(declare-fun Anon1 () Int)
(declare-fun nc6 () Int)
(declare-fun v51_9150 () Int)
(declare-fun v52_9151 () Int)
(declare-fun v50prm () node)
(declare-fun res () node)
(declare-fun nc () Int)
(declare-fun nb () Int)
(declare-fun h () Int)
(declare-fun na () Int)


(assert 
(exists ((flted139 Int)(flted140 Int)(flted141 Int)(v51prm Int)(v52prm Int)(tmpprm node))(and 
;lexvar(= cl 1)
(<= Anon9 1)
(<= 0 Anon9)
(<= 1 bhr13)
(<= 0 nr13)
(= bh bhr13)
(= cl Anon9)
(= n nr13)
(= flted118 0)
(= flted119 0)
(= nb (+ (+ nr13 1) nl13))
(= bhl13 bhr13)
(= flted121 (+ bhl13 1))
(= aprm a)
(= bprm b)
(= cprm c)
(= flted120 0)
(= flted121 (+ 1 h))
(= flted122 0)
(= flted123 (+ 1 h))
(distinct b nil)
(distinct c nil)
(= na6 na)
(= h21 h)
(= nb6 nl13)
(= Anon1 Anon8)
(= nc6 n)
(<= 0 n)
(<= 1 bh)
(<= 0 cl)
(<= cl 1)
(<= 0 nl13)
(<= 1 bhl13)
(<= 0 Anon8)
(<= Anon8 1)
(<= 0 na)
(<= 1 h)
(<= 0 flted120)
(<= flted120 1)
(= flted139 (+ (+ (+ 2 nb6) na6) nc6))
(= flted140 1)
(= flted141 (+ 1 h21))
(= v51prm 0)
(= v52prm 0)
(= res v50prm)
(tobool (ssep 
(pto bprm (sref (ref val v21) (ref color flted118) (ref left l13) (ref right r13) ))
(rb c nc flted122 flted123)
(rb tmpprm flted139 flted140 flted141)
(pto v50prm (sref (ref val v51prm) (ref color v52prm) (ref left tmpprm) (ref right cprm) ))
) )
))
)

(assert (not 
(exists ((flted133 Int)(flted134 Int)(flted135 Int))(and 
(= flted133 (+ 2 h))
(= flted134 0)
(= flted135 (+ (+ (+ 2 nb) na) nc))
(<= 0 nc)
(<= 0 nb)
(<= 1 h)
(<= 0 na)
(tobool  
(rb res flted135 flted134 flted133)
 )
))
))

(check-sat)