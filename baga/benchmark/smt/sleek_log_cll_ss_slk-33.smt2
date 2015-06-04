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












































(declare-fun Anon5 () Int)
(declare-fun Anon6_737 () Int)
(declare-fun r6_738 () node)
(declare-fun x () node)
(declare-fun n () Int)
(declare-fun r5 () node)
(declare-fun xprm () node)
(declare-fun p5_735 () node)
(declare-fun v10prm () node)
(declare-fun self4 () node)
(declare-fun flted6_736 () Int)
(declare-fun flted5 () Int)


(assert 
(exists ((p5 node)(flted6 Int)(Anon6 Int)(r6 node))(and 
;lexvar(= v10prm r5)
(= (+ flted5 1) n)
(= self4 xprm)
(= xprm x)
(< 0 n)
(distinct r5 xprm)
(= p5 self4)
(distinct v10prm self4)
(= (+ flted6 1) flted5)
(tobool (ssep 
(pto xprm (sref (ref val Anon5) (ref next r5) ))
(pto v10prm (sref (ref val Anon6) (ref next r6) ))
(cll r6 p5 flted6)
) )
))
)

(assert (not 
(and 
(tobool  
(pto v10prm (sref (ref val val4prm) (ref next next4prm) ))
 )
)
))

(check-sat)