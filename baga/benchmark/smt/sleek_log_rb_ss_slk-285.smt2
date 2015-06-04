(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


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





































































































































































































































































































































































(declare-fun x () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun xprm () node)
(declare-fun cl () Int)
(declare-fun bh () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= xprm x)
(= aprm a)
(<= 0 cl)
(<= cl 1)
(= xprm nil)
(tobool  
(rb x n cl bh)
 )
)
)

(assert (not 
(exists ((bh31 Int)(flted330 Int)(cl22 Int))(and 
(= bh31 bh)
(<= cl22 1)
(<= 0 cl22)
(= cl 1)
(= (+ flted330 1) n)
(<= cl 1)
(<= 0 cl)
(<= 1 bh)
(<= 0 n)
(tobool  
(rb xprm flted330 cl22 bh31)
 )
))
))

(check-sat)