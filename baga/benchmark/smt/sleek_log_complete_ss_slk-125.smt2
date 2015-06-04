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
(declare-fun nmin () Int)
(declare-fun n () Int)
(declare-fun v20prm () node2)
(declare-fun v () node2)
(declare-fun tprm () node2)
(declare-fun t () node2)
(declare-fun nmin27 () Int)
(declare-fun flted21 () Int)
(declare-fun nmin29 () Int)
(declare-fun n7 () Int)
(declare-fun nmin28 () Int)
(declare-fun flted20 () Int)
(declare-fun nmin37 () Int)
(declare-fun n11 () Int)
(declare-fun tmpprm () node2)
(declare-fun r10 () node2)
(declare-fun nmin32 () Int)
(declare-fun n8 () Int)
(declare-fun nmin43 () Int)
(declare-fun n15 () Int)
(declare-fun nmin38 () Int)
(declare-fun n12 () Int)
(declare-fun nmin44 () Int)
(declare-fun n16 () Int)
(declare-fun v33prm () Int)
(declare-fun v35prm () Int)


(assert 
(and 
;lexvar(<= n12 nmin37)
(<= n8 nmin29)
(= (+ flted21 1) n)
(= (+ flted20 2) n)
(distinct tprm nil)
(< nmin n)
(= v20prm v)
(= tprm t)
(= n7 flted21)
(= nmin29 nmin27)
(<= 0 nmin27)
(<= nmin27 flted21)
(= n8 n7)
(= nmin32 nmin29)
(<= 0 nmin29)
(<= nmin29 n7)
(= n11 flted20)
(= nmin37 nmin28)
(<= 0 nmin28)
(<= nmin28 flted20)
(= n12 n11)
(= nmin38 nmin37)
(<= 0 nmin37)
(<= nmin37 n11)
(= tmpprm r10)
(= n15 n8)
(= nmin43 nmin32)
(<= 0 nmin32)
(<= nmin32 n8)
(= v33prm n15)
(<= 0 nmin43)
(<= nmin43 n15)
(= n16 n12)
(= nmin44 nmin38)
(<= 0 nmin38)
(<= nmin38 n12)
(= v35prm n16)
(<= 0 nmin44)
(<= nmin44 n16)
(distinct v33prm v35prm)
(tobool (ssep 
(pto tprm (sref (ref val Anon10) (ref left l10) (ref right r10) ))
(complete l10 n15 nmin43)
(complete r10 n16 nmin44)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)