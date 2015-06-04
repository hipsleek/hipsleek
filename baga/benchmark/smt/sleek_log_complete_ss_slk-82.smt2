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









































































































































































(declare-fun Anon11 () Int)
(declare-fun r11 () node2)
(declare-fun l11 () node2)
(declare-fun flted22 () Int)
(declare-fun nmin31 () Int)
(declare-fun nmin () Int)
(declare-fun n () Int)
(declare-fun v20prm () node2)
(declare-fun v () node2)
(declare-fun tprm () node2)
(declare-fun t () node2)
(declare-fun nmin30 () Int)
(declare-fun flted23 () Int)
(declare-fun nmin29 () Int)
(declare-fun n7 () Int)
(declare-fun nmin32 () Int)
(declare-fun n8 () Int)
(declare-fun v25prm () Int)
(declare-fun v23prm () Int)


(assert 
(and 
;lexvar(= (+ flted23 1) n)
(= (+ flted22 1) n)
(distinct tprm nil)
(< nmin n)
(= v20prm v)
(= tprm t)
(= n7 flted23)
(= nmin29 nmin30)
(<= 0 nmin30)
(<= nmin30 flted23)
(= v23prm nmin29)
(= n8 n7)
(= nmin32 nmin29)
(<= 0 nmin29)
(<= nmin29 n7)
(= v25prm n8)
(<= 0 nmin32)
(<= nmin32 n8)
(<= v25prm v23prm)
(tobool (ssep 
(pto tprm (sref (ref val Anon11) (ref left l11) (ref right r11) ))
(complete r11 flted22 nmin31)
(complete l11 n8 nmin32)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)