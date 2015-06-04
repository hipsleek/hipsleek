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






























































(declare-fun v6prm () node2)
(declare-fun v7prm () Int)
(declare-fun v5_130 () Int)
(declare-fun v2prm () Int)
(declare-fun v3prm () Int)
(declare-fun n () Int)
(declare-fun nprm () Int)


(assert 
(exists ((v5prm Int))(and 
;lexvar(= v7prm 1)
(= (+ v5prm 1) nprm)
(= v2prm 0)
(= v3prm 0)
(= nprm n)
(distinct nprm 0)
(tobool (ssep 
(perfect v6prm v5prm)
(htrue )
) )
))
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)