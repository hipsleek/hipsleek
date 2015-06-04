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
(declare-fun v21 () Int)
(declare-fun nc () Int)
(declare-fun r13 () node)
(declare-fun v22_6717 () Int)
(declare-fun l14_6718 () node)
(declare-fun r14_6721 () node)
(declare-fun v41prm () node)
(declare-fun l13 () node)
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
(declare-fun bhr14_6723 () Int)
(declare-fun bhl14_6720 () Int)
(declare-fun bh3 () Int)
(declare-fun n3 () Int)
(declare-fun nl14_6719 () Int)
(declare-fun nr14_6722 () Int)
(declare-fun flted124_6714 () Int)
(declare-fun flted125_6715 () Int)
(declare-fun flted126_6716 () Int)


(assert 
(exists ((flted124 Int)(flted125 Int)(flted126 Int)(v22 Int)(l14 node)(nl14 Int)(bhl14 Int)(r14 node)(nr14 Int)(bhr14 Int))(and 
;lexvar(= v41prm l13)
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
(= bhr14 bh3)
(= bhl14 bh3)
(= n3 (+ (+ nr14 1) nl14))
(= flted124 0)
(= flted125 0)
(= flted126 1)
(tobool (ssep 
(rb a na flted120 h)
(pto bprm (sref (ref val v21) (ref color flted118) (ref left l13) (ref right r13) ))
(rb c nc flted122 flted123)
(rb r13 n cl bh)
(pto v41prm (sref (ref val v22) (ref color flted126) (ref left l14) (ref right r14) ))
(rb l14 nl14 flted125 bhl14)
(rb r14 nr14 flted124 bhr14)
) )
))
)

(assert (not 
(and 
(tobool  
(pto v41prm (sref (ref val val7prm) (ref color color8prm) (ref left left7prm) (ref right right7prm) ))
 )
)
))

(check-sat)