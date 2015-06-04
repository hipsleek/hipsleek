(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


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
(declare-fun r10 () node2)
(declare-fun auxprm () node2)
(declare-fun l10 () node2)
(declare-fun nmin32 () Int)
(declare-fun n7 () NUM)
(declare-fun t () node2)
(declare-fun v20prm () node2)
(declare-fun v () node2)
(declare-fun tprm () node2)
(declare-fun nmin () NUM)
(declare-fun nmin27 () Int)
(declare-fun nmin28 () Int)
(declare-fun flted20 () Int)
(declare-fun flted21 () NUM)
(declare-fun n () NUM)
(declare-fun nmin29 () Int)
(declare-fun n8 () Int)


(assert 
(and 
;lexvar(= auxprm l10)
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
(< nmin29 n8)
(tobool (ssep 
(pto tprm (sref (ref val Anon10) (ref left l10) (ref right r10) ))
(complete r10 flted20 nmin28)
(complete l10 n8 nmin32)
) )
)
)

(assert (not 
(and 
(= nmin34 n10)
(tobool  
(complete auxprm n10 nmin34)
 )
)
))

(check-sat)