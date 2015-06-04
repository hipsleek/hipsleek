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









































































































































































(declare-fun Anon10 () Int)
(declare-fun l10 () node2)
(declare-fun aux_6483 () node2)
(declare-fun right () node2)
(declare-fun r10 () node2)
(declare-fun nmin51 () Int)
(declare-fun nmin39 () Int)
(declare-fun n13 () Int)
(declare-fun nmin38 () Int)
(declare-fun n11 () NUM)
(declare-fun nmin32 () Int)
(declare-fun n7 () NUM)
(declare-fun t () node2)
(declare-fun v20prm () node2)
(declare-fun v () node2)
(declare-fun tprm () node2)
(declare-fun nmin27 () Int)
(declare-fun nmin28 () Int)
(declare-fun flted20 () NUM)
(declare-fun flted21 () NUM)
(declare-fun n8 () Int)
(declare-fun nmin29 () Int)
(declare-fun nmin37 () Int)
(declare-fun n12 () Int)
(declare-fun n () Int)
(declare-fun nmin () Int)


(assert 
(exists ((auxprm node2))(and 
;lexvar(= right r10)
(<= nmin39 n13)
(<= 0 nmin39)
(<= nmin38 n12)
(<= 0 nmin38)
(= nmin39 nmin38)
(= n13 n12)
(<= nmin37 n11)
(<= 0 nmin37)
(= nmin38 nmin37)
(= n12 n11)
(<= nmin28 flted20)
(<= 0 nmin28)
(= nmin37 nmin28)
(= n11 flted20)
(<= nmin32 n8)
(<= 0 nmin32)
(<= nmin29 n7)
(<= 0 nmin29)
(= nmin32 nmin29)
(= n8 n7)
(<= nmin27 flted21)
(<= 0 nmin27)
(= nmin29 nmin27)
(= n7 flted21)
(= tprm t)
(= v20prm v)
(< nmin n)
(distinct tprm nil)
(= (+ flted20 2) n)
(= (+ flted21 1) n)
(<= n8 nmin29)
(< nmin37 n12)
(tobool (ssep 
(complete l10 n8 nmin32)
(complete auxprm n13 nmin51)
(pto tprm (sref (ref val Anon10) (ref left l10) (ref right auxprm) ))
) )
))
)

(assert (not 
(exists ((n19 Int)(nmin49 Int))(and 
(= n19 n)
(<= nmin n)
(<= 0 nmin)
(tobool  
(complete tprm n19 nmin49)
 )
))
))

(check-sat)