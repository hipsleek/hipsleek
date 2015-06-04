(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node2 0)
(declare-fun val () (Field node2 Int))
(declare-fun flag () (Field node2 Int))
(declare-fun left () (Field node2 node2))
(declare-fun right () (Field node2 node2))

(define-fun perfect ((?in node2) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_28_29 Int)(?flted_28_30 Int))(and 
(= (+ ?flted_28_30 1) ?n)
(= (+ ?flted_28_29 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref flag ?Anon_15) (ref left ?l) (ref right ?r) ))
(perfect ?l ?flted_28_30)
(perfect ?r ?flted_28_29)
) )
)))))






























































(declare-fun Anon4_767 () Int)
(declare-fun Anon5_768 () Int)
(declare-fun l2_769 () node2)
(declare-fun r2_770 () node2)
(declare-fun t () node2)
(declare-fun aprm () node2)
(declare-fun a () node2)
(declare-fun tprm () node2)
(declare-fun flted4_765 () Int)
(declare-fun flted5_766 () Int)
(declare-fun n () Int)


(assert 
(exists ((flted4 Int)(flted5 Int)(Anon4 Int)(Anon5 Int)(l2 node2)(r2 node2))(and 
;lexvar(= tprm t)
(= aprm a)
(distinct tprm nil)
(= (+ flted4 1) n)
(= (+ flted5 1) n)
(tobool (ssep 
(pto tprm (sref (ref val Anon4) (ref flag Anon5) (ref left l2) (ref right r2) ))
(perfect l2 flted5)
(perfect r2 flted4)
) )
))
)

(assert (not 
(and 
(tobool  
(pto tprm (sref (ref val val2prm) (ref flag flag2prm) (ref left left2prm) (ref right right2prm) ))
 )
)
))

(check-sat)