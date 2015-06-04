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









































































































































































(declare-fun Anon4_1365 () Int)
(declare-fun l4_1366 () node2)
(declare-fun r4_1368 () node2)
(declare-fun t () node2)
(declare-fun tprm () node2)
(declare-fun nmin () Int)
(declare-fun nmin12_1367 () Int)
(declare-fun nmin13_1369 () Int)
(declare-fun flted8_1363 () Int)
(declare-fun flted9_1364 () Int)
(declare-fun n () Int)


(assert 
(exists ((flted8 Int)(flted9 Int)(Anon4 Int)(l4 node2)(nmin12 Int)(r4 node2)(nmin13 Int))(and 
;lexvar(= tprm t)
(distinct tprm nil)
(= (+ flted8 2) n)
(= (+ flted9 1) n)
(tobool (ssep 
(pto tprm (sref (ref val Anon4) (ref left l4) (ref right r4) ))
(complete l4 flted9 nmin12)
(complete r4 flted8 nmin13)
) )
))
)

(assert (not 
(and 
(tobool  
(pto tprm (sref (ref val val2prm) (ref left left2prm) (ref right right2prm) ))
 )
)
))

(check-sat)