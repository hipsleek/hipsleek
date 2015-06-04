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









































































































































































(declare-fun Anon8_2488 () Int)
(declare-fun l8_2489 () node2)
(declare-fun r8_2491 () node2)
(declare-fun t () node2)
(declare-fun v20prm () node2)
(declare-fun v () node2)
(declare-fun tprm () node2)
(declare-fun nmin () NUM)
(declare-fun nmin23_2490 () Int)
(declare-fun nmin24_2492 () Int)
(declare-fun flted16_2486 () Int)
(declare-fun flted17_2487 () Int)
(declare-fun n () NUM)


(assert 
(exists ((flted16 Int)(flted17 Int)(Anon8 Int)(l8 node2)(nmin23 Int)(r8 node2)(nmin24 Int))(and 
;lexvar(= tprm t)
(= v20prm v)
(< nmin n)
(distinct tprm nil)
(= (+ flted16 2) n)
(= (+ flted17 1) n)
(tobool (ssep 
(pto tprm (sref (ref val Anon8) (ref left l8) (ref right r8) ))
(complete l8 flted17 nmin23)
(complete r8 flted16 nmin24)
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