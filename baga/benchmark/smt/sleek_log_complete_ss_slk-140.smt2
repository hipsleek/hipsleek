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









































































































































































(declare-fun Anon12_6984 () Int)
(declare-fun l12_6985 () node2)
(declare-fun r12_6987 () node2)
(declare-fun t () node2)
(declare-fun v20prm () node2)
(declare-fun v () node2)
(declare-fun tprm () node2)
(declare-fun nmin () Int)
(declare-fun nmin54_6986 () Int)
(declare-fun nmin55_6988 () Int)
(declare-fun flted26_6982 () Int)
(declare-fun flted27_6983 () Int)
(declare-fun n () Int)


(assert 
(exists ((flted26 Int)(flted27 Int)(Anon12 Int)(l12 node2)(nmin54 Int)(r12 node2)(nmin55 Int))(and 
;lexvar(= tprm t)
(= v20prm v)
(= nmin n)
(distinct tprm nil)
(= (+ flted26 1) n)
(= (+ flted27 1) n)
(tobool (ssep 
(pto tprm (sref (ref val Anon12) (ref left l12) (ref right r12) ))
(complete l12 flted27 nmin54)
(complete r12 flted26 nmin55)
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