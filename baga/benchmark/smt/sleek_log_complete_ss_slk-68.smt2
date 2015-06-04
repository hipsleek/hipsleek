(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node2 0)
(declare-fun val () (Field node2 Int))
(declare-fun left () (Field node2 node2))
(declare-fun right () (Field node2 node2))

(define-fun complete ((?in node2) (?n Int) (?nmin Int))
Space (tospace
(or
(or
(and 
(= ?in nil)
(= ?n 0)
(= ?nmin 0)

)(exists ((?flted_25_33 Int)(?flted_25_34 Int))(and 
(= (+ ?flted_25_34 1) ?n)
(= (+ ?flted_25_33 2) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref left ?l) (ref right ?r) ))
(complete ?l ?flted_25_34 ?nmin1)
(complete ?r ?flted_25_33 ?nmin2)
) )
)))(exists ((?flted_26_35 Int)(?flted_26_36 Int))(and 
(= (+ ?flted_26_36 1) ?n)
(= (+ ?flted_26_35 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref left ?l) (ref right ?r) ))
(complete ?l ?flted_26_36 ?nmin1)
(complete ?r ?flted_26_35 ?nmin2)
) )
)))))









































































































































































(declare-fun Anon9_2528 () Int)
(declare-fun l9_2529 () node2)
(declare-fun r9_2531 () node2)
(declare-fun t () node2)
(declare-fun v20prm () node2)
(declare-fun v () node2)
(declare-fun tprm () node2)
(declare-fun nmin () NUM)
(declare-fun nmin25_2530 () Int)
(declare-fun nmin26_2532 () Int)
(declare-fun flted18_2526 () Int)
(declare-fun flted19_2527 () Int)
(declare-fun n () NUM)


(assert 
(exists ((flted18 Int)(flted19 Int)(Anon9 Int)(l9 node2)(nmin25 Int)(r9 node2)(nmin26 Int))(and 
;lexvar(= tprm t)
(= v20prm v)
(< nmin n)
(distinct tprm nil)
(= (+ flted18 1) n)
(= (+ flted19 1) n)
(tobool (ssep 
(pto tprm (sref (ref val Anon9) (ref left l9) (ref right r9) ))
(complete l9 flted19 nmin25)
(complete r9 flted18 nmin26)
) )
))
)

(assert (not 
(and 
(tobool  
(pto tprm (sref (ref val val4prm) (ref left left4prm) (ref right right4prm) ))
 )
)
))

(check-sat)