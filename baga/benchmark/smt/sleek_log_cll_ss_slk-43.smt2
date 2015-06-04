(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun cll ((?in node) (?p node) (?n Int))
Space (tospace
(or
(and 
(= ?in ?p)
(= ?n 0)

)(exists ((?p_28 node)(?flted_11_27 Int))(and 
(= (+ ?flted_11_27 1) ?n)
(distinct ?in ?p)
(= ?p_28 ?p)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?r) ))
(cll ?r ?p_28 ?flted_11_27)
) )
)))))

(define-fun hd ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?self_25 node)(?flted_15_24 Int))(and 
(= (+ ?flted_15_24 1) ?n)
(= ?self_25 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref next ?r) ))
(cll ?r ?self_25 ?flted_15_24)
) )
)))))












































(declare-fun tmp2_1031 () node)
(declare-fun res () node)
(declare-fun next3 () node)
(declare-fun v4 () Int)
(declare-fun next2 () node)
(declare-fun v2 () Int)


(assert 
(exists ((tmp2prm node))(and 
;lexvar(= res next3)
(= v4 20)
(= next2 nil)
(= v2 10)
(tobool (ssep 
(pto tmp2prm (sref (ref val v4) (ref next next3) ))
(pto next3 (sref (ref val v2) (ref next tmp2prm) ))
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