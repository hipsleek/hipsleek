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






























































(declare-fun nprm () Int)
(declare-fun n9 () Int)
(declare-fun aprm () node2)
(declare-fun a () node2)
(declare-fun tprm () node2)
(declare-fun t () node2)
(declare-fun n8 () Int)
(declare-fun n () Int)


(assert 
(and 
;lexvar(<= 0 n9)
(= nprm n9)
(<= 0 n8)
(= n9 n8)
(= aprm a)
(= tprm t)
(= n8 n)
(<= 0 n)
(tobool  
(perfect tprm n9)
 )
)
)

(assert (not 
;lexvar
))

(check-sat)