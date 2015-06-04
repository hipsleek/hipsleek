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






























































(declare-fun tprm () node2)
(declare-fun new_1381 () node2)
(declare-fun t1 () node2)
(declare-fun t () node2)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun n8 () Int)
(declare-fun v34_1380 () Int)
(declare-fun n9_1383 () Int)
(declare-fun n9 () Int)
(declare-fun n () Int)


(assert 
(exists ((v34prm Int)(newprm node2)(siprm boolean))(and 
;lexvar(<= 0 n)
(= n8 n)
(= t1 t)
(= aprm a)
(= n9 n8)
(<= 0 n8)
(<= 0 n9)
(= v34prm 1)
(tobool (ssep 
(pto tprm (sref (ref val aprm) (ref flag v34prm) (ref left t1) (ref right newprm) ))
(perfect t1 n9)
(perfect newprm n9)
) )
))
)

(assert (not 
(exists ((n10 Int))(and 
(<= 0 n)
(tobool  
(perfect tprm n10)
 )
))
))

(check-sat)