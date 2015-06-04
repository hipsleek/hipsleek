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









































































































































































(declare-fun Anon6 () Int)
(declare-fun l6 () node2)
(declare-fun r6 () node2)
(declare-fun tprm () node2)
(declare-fun nmin16 () Int)
(declare-fun flted13 () Int)
(declare-fun n4 () Int)
(declare-fun nmin17 () Int)
(declare-fun flted12 () Int)
(declare-fun n5 () Int)
(declare-fun nmin21 () Int)
(declare-fun nmin18 () Int)
(declare-fun v17_2185 () Int)
(declare-fun v18prm () Int)
(declare-fun t () node2)
(declare-fun res () Int)
(declare-fun n () Int)
(declare-fun nmin () Int)


(assert 
(exists ((v17prm Int))(and 
;lexvar(= (+ flted13 1) n)
(= (+ flted12 2) n)
(distinct tprm nil)
(= tprm t)
(= n4 flted13)
(= nmin18 nmin16)
(<= 0 nmin16)
(<= nmin16 flted13)
(<= 0 nmin18)
(<= nmin18 n4)
(= n5 flted12)
(= nmin21 nmin17)
(<= 0 nmin17)
(<= nmin17 flted12)
(<= 0 nmin21)
(<= nmin21 n5)
(= v18prm (+ 1 v17prm))
(= res v18prm)
(tobool (ssep 
(pto tprm (sref (ref val Anon6) (ref left l6) (ref right r6) ))
(complete l6 n4 nmin18)
(complete r6 n5 nmin21)
) )
))
)

(assert (not 
(exists ((n6 Int)(nmin22 Int))(and 
(= nmin22 nmin)
(= n6 n)
(= res nmin)
(<= nmin n)
(<= 0 nmin)
(tobool  
(complete t n6 nmin22)
 )
))
))

(check-sat)