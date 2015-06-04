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






























































(declare-fun v6_222 () node2)
(declare-fun v11_223 () node2)
(declare-fun v3_220 () Int)
(declare-fun v2_221 () Int)
(declare-fun v () Int)
(declare-fun v8_219 () Int)
(declare-fun nprm () Int)
(declare-fun v10prm () node2)
(declare-fun res () node2)
(declare-fun n () Int)


(assert 
(exists ((v8prm Int)(v3prm Int)(v2prm Int)(v6prm node2)(v11prm node2))(and 
;lexvar(distinct nprm 0)
(= nprm n)
(= v3prm 0)
(= v2prm 0)
(= (+ v 1) nprm)
(= (+ v8prm 1) nprm)
(= res v10prm)
(tobool (ssep 
(perfect v6prm v)
(perfect v11prm v8prm)
(pto v10prm (sref (ref val v3prm) (ref flag v2prm) (ref left v6prm) (ref right v11prm) ))
) )
))
)

(assert (not 
(exists ((n1 Int))(and 
(= n1 n)
(tobool  
(perfect res n1)
 )
))
))

(check-sat)