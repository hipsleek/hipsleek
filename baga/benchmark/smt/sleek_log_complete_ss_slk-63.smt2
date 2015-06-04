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









































































































































































(declare-fun Anon7 () Int)
(declare-fun l7 () node2)
(declare-fun r7 () node2)
(declare-fun tprm () node2)
(declare-fun nmin19 () Int)
(declare-fun flted15 () Int)
(declare-fun n4 () Int)
(declare-fun nmin20 () Int)
(declare-fun flted14 () Int)
(declare-fun n5 () Int)
(declare-fun nmin21 () Int)
(declare-fun nmin18 () Int)
(declare-fun v17_2308 () Int)
(declare-fun v18prm () Int)
(declare-fun t () node2)
(declare-fun res () Int)
(declare-fun n () Int)
(declare-fun nmin () Int)


(assert 
(exists ((v17prm Int))(and 
;lexvar(= (+ flted15 1) n)
(= (+ flted14 1) n)
(distinct tprm nil)
(= tprm t)
(= n4 flted15)
(= nmin18 nmin19)
(<= 0 nmin19)
(<= nmin19 flted15)
(<= 0 nmin18)
(<= nmin18 n4)
(= n5 flted14)
(= nmin21 nmin20)
(<= 0 nmin20)
(<= nmin20 flted14)
(<= 0 nmin21)
(<= nmin21 n5)
(= v18prm (+ 1 v17prm))
(= res v18prm)
(tobool (ssep 
(pto tprm (sref (ref val Anon7) (ref left l7) (ref right r7) ))
(complete l7 n4 nmin18)
(complete r7 n5 nmin21)
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