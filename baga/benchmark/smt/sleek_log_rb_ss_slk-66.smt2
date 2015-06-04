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
(declare-fun r13 () node)
(declare-fun l13 () node)
(declare-fun v23 () Int)
(declare-fun l15 () node)
(declare-fun r15 () node)
(declare-fun tmp_8551 () node)
(declare-fun flted129 () Int)
(declare-fun bh3 () Int)
(declare-fun cl3 () Int)
(declare-fun Anon8 () Int)
(declare-fun n3 () Int)
(declare-fun flted123 () Int)
(declare-fun flted122 () Int)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun flted121 () Int)
(declare-fun bhl13 () Int)
(declare-fun nl13 () Int)
(declare-fun flted119 () Int)
(declare-fun flted118 () Int)
(declare-fun nr13 () Int)
(declare-fun bhr13 () Int)
(declare-fun Anon9 () Int)
(declare-fun n () Int)
(declare-fun bh () Int)
(declare-fun cl () Int)
(declare-fun nr15 () Int)
(declare-fun bhr15 () Int)
(declare-fun flted127 () Int)
(declare-fun nl15 () Int)
(declare-fun bhl15 () Int)
(declare-fun flted128 () Int)
(declare-fun flted120 () Int)
(declare-fun flted136_8546 () Int)
(declare-fun flted137_8547 () Int)
(declare-fun flted138_8548 () Int)
(declare-fun na5 () Int)
(declare-fun h14 () Int)
(declare-fun nb5 () Int)
(declare-fun nc5 () Int)
(declare-fun nd () Int)
(declare-fun v51_8549 () Int)
(declare-fun v52_8550 () Int)
(declare-fun v50prm () node)
(declare-fun res () node)
(declare-fun nc () Int)
(declare-fun nb () Int)
(declare-fun h () Int)
(declare-fun na () Int)


(assert 
(exists ((flted136 Int)(flted137 Int)(flted138 Int)(v51prm Int)(v52prm Int)(tmpprm node))(and 
;lexvar(= flted129 1)
(= flted128 0)
(= flted127 0)
(= n3 (+ (+ nr15 1) nl15))
(= bhl15 bh3)
(= bhr15 bh3)
(<= cl3 1)
(<= 0 cl3)
(<= 1 bh3)
(<= 0 n3)
(= cl3 1)
(<= Anon8 1)
(<= 0 Anon8)
(<= 1 bhl13)
(<= 0 nl13)
(= bh3 bhl13)
(= cl3 Anon8)
(= n3 nl13)
(distinct c nil)
(distinct b nil)
(= flted123 (+ 1 h))
(= flted122 0)
(= flted121 (+ 1 h))
(= flted120 0)
(= cprm c)
(= bprm b)
(= aprm a)
(= flted121 (+ bhl13 1))
(= bhl13 bhr13)
(= nb (+ (+ nr13 1) nl13))
(= flted119 0)
(= flted118 0)
(= n nr13)
(= cl Anon9)
(= bh bhr13)
(<= 0 nr13)
(<= 1 bhr13)
(<= 0 Anon9)
(<= Anon9 1)
(= cl 0)
(= na5 na)
(= h14 h)
(= nb5 nl15)
(= nc5 nr15)
(= nd n)
(<= 0 n)
(<= 1 bh)
(<= 0 cl)
(<= cl 1)
(<= 0 nr15)
(<= 1 bhr15)
(<= 0 flted127)
(<= flted127 1)
(<= 0 nl15)
(<= 1 bhl15)
(<= 0 flted128)
(<= flted128 1)
(<= 0 na)
(<= 1 h)
(<= 0 flted120)
(<= flted120 1)
(= flted136 (+ (+ (+ (+ 3 nc5) na5) nb5) nd))
(= flted137 1)
(= flted138 (+ 1 h14))
(= v51prm 0)
(= v52prm 0)
(= res v50prm)
(tobool (ssep 
(pto bprm (sref (ref val v21) (ref color flted118) (ref left l13) (ref right r13) ))
(rb c nc flted122 flted123)
(pto l13 (sref (ref val v23) (ref color flted129) (ref left l15) (ref right r15) ))
(rb tmpprm flted136 flted137 flted138)
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