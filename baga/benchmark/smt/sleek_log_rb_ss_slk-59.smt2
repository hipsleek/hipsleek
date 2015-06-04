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
(declare-fun nc () Int)
(declare-fun l13 () node)
(declare-fun v23 () Int)
(declare-fun nd () Int)
(declare-fun nc5 () Int)
(declare-fun nb5 () Int)
(declare-fun h14 () Int)
(declare-fun na5 () node)
(declare-fun na () node)
(declare-fun v46prm () Int)
(declare-fun v45prm () node)
(declare-fun r13 () node)
(declare-fun v44prm () node)
(declare-fun r15 () node)
(declare-fun v42prm () node)
(declare-fun l15 () node)
(declare-fun bh () Int)
(declare-fun cl () Int)
(declare-fun Anon9 () Int)
(declare-fun n () Int)
(declare-fun flted118 () Int)
(declare-fun flted119 () Int)
(declare-fun nb () Int)
(declare-fun nr13 () Int)
(declare-fun bhr13 () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun cprm () node)
(declare-fun flted120 () Int)
(declare-fun flted121 () Int)
(declare-fun flted122 () Int)
(declare-fun flted123 () Int)
(declare-fun h () Int)
(declare-fun b () node)
(declare-fun c () node)
(declare-fun nl13 () Int)
(declare-fun bhl13 () Int)
(declare-fun Anon8 () Int)
(declare-fun cl3 () Int)
(declare-fun bhr15 () Int)
(declare-fun bhl15 () Int)
(declare-fun bh3 () Int)
(declare-fun n3 () Int)
(declare-fun nl15 () Int)
(declare-fun nr15 () Int)
(declare-fun flted127 () Int)
(declare-fun flted128 () Int)
(declare-fun flted129 () Int)


(assert 
(and 
;lexvar(= nd n)
(= nc5 nr15)
(= nb5 nl15)
(= h14 h)
(= na5 na)
(= v46prm 1)
(= v45prm r13)
(= v44prm r15)
(= v42prm l15)
(<= cl 1)
(<= 0 cl)
(<= 1 bh)
(<= 0 n)
(= cl 0)
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
(= n3 nl13)
(= cl3 Anon8)
(= bh3 bhl13)
(<= 0 nl13)
(<= 1 bhl13)
(<= 0 Anon8)
(<= Anon8 1)
(= cl3 1)
(<= 0 n3)
(<= 1 bh3)
(<= 0 cl3)
(<= cl3 1)
(= bhr15 bh3)
(= bhl15 bh3)
(= n3 (+ (+ nr15 1) nl15))
(= flted127 0)
(= flted128 0)
(= flted129 1)
(tobool (ssep 
(pto bprm (sref (ref val v21) (ref color flted118) (ref left l13) (ref right r13) ))
(rb c nc flted122 flted123)
(pto l13 (sref (ref val v23) (ref color flted129) (ref left l15) (ref right r15) ))
) )
)
)

(assert (not 
;lexvar
))

(check-sat)