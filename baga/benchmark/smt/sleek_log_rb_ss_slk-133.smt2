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





































































































































































































































































































































































(declare-fun v41 () Int)
(declare-fun l29 () node)
(declare-fun Anon19 () Int)
(declare-fun r29 () node)
(declare-fun Anon20 () Int)
(declare-fun xprm () node)
(declare-fun bhl29 () Int)
(declare-fun bhr29 () Int)
(declare-fun nl29 () Int)
(declare-fun nr29 () Int)
(declare-fun flted258 () Int)
(declare-fun x () node)
(declare-fun cl () Int)
(declare-fun bh () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= res v97prm)
(= xprm x)
(distinct xprm nil)
(= bh (+ bhl29 1))
(= bhl29 bhr29)
(= n (+ (+ nr29 1) nl29))
(= cl 0)
(= flted258 0)
(tobool (ssep 
(pto xprm (sref (ref val v41) (ref color flted258) (ref left l29) (ref right r29) ))
(rb l29 nl29 Anon19 bhl29)
(rb r29 nr29 Anon20 bhr29)
) )
)
)

(assert (not 
(exists ((n8 Int)(cl6 Int)(bh6 Int))(and 
(= bh6 bh)
(= cl6 cl)
(= n8 n)
(= cl 0)
(<= cl 1)
(<= 0 cl)
(<= 1 bh)
(<= 0 n)
(tobool  
(rb x n8 cl6 bh6)
 )
))
))

(check-sat)