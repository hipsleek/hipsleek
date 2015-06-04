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









































































































































































(declare-fun Anon11 () Int)
(declare-fun l11 () node2)
(declare-fun auxprm () node2)
(declare-fun r11 () node2)
(declare-fun nmin38 () Int)
(declare-fun n11 () NUM)
(declare-fun nmin32 () Int)
(declare-fun n7 () NUM)
(declare-fun t () node2)
(declare-fun v20prm () node2)
(declare-fun v () node2)
(declare-fun tprm () node2)
(declare-fun nmin () NUM)
(declare-fun nmin30 () Int)
(declare-fun nmin31 () Int)
(declare-fun flted22 () NUM)
(declare-fun flted23 () NUM)
(declare-fun n () NUM)
(declare-fun n8 () Int)
(declare-fun nmin29 () Int)
(declare-fun nmin37 () Int)
(declare-fun n12 () Int)


(assert 
(and 
;lexvar(= auxprm r11)
(<= nmin38 n12)
(<= 0 nmin38)
(<= nmin37 n11)
(<= 0 nmin37)
(= nmin38 nmin37)
(= n12 n11)
(<= nmin31 flted22)
(<= 0 nmin31)
(= nmin37 nmin31)
(= n11 flted22)
(<= nmin32 n8)
(<= 0 nmin32)
(<= nmin29 n7)
(<= 0 nmin29)
(= nmin32 nmin29)
(= n8 n7)
(<= nmin30 flted23)
(<= 0 nmin30)
(= nmin29 nmin30)
(= n7 flted23)
(= tprm t)
(= v20prm v)
(< nmin n)
(distinct tprm nil)
(= (+ flted22 1) n)
(= (+ flted23 1) n)
(<= n8 nmin29)
(< nmin37 n12)
(tobool (ssep 
(pto tprm (sref (ref val Anon11) (ref left l11) (ref right r11) ))
(complete l11 n8 nmin32)
(complete r11 n12 nmin38)
) )
)
)

(assert (not 
(and 
(= nmin40 n14)
(tobool  
(complete auxprm n14 nmin40)
 )
)
))

(check-sat)