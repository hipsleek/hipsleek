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

(define-fun sll ((?in node) (?n Int) (?sm NUM) (?lg Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)
(<= ?sm ?lg)

)(exists ((?flted_16_26 Int)(?qs_27 Int)(?ql_28 Int))(and 
(= (+ ?flted_16_26 1) ?n)
(<= ?qmin ?qs_27)
(<= ?ql_28 ?lg)
(<= ?sm ?qmin)
(tobool (ssep 
(pto ?in (sref (ref val ?qmin) (ref next ?q) ))
(sll ?q ?flted_16_26 ?qs_27 ?ql_28)
) )
)))))

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_11_30 Int))(and 
(= (+ ?flted_11_30 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q ?flted_11_30)
) )
)))))










































































(declare-fun v6prm () node)
(declare-fun nres_437 () Int)
(declare-fun lres_436 () Int)
(declare-fun sres_435 () Int)
(declare-fun xl1 () Int)
(declare-fun xs1 () NUM)
(declare-fun n1 () Int)
(declare-fun tmpprm () node)
(declare-fun q1 () node)
(declare-fun x () node)
(declare-fun v () Int)
(declare-fun xprm () node)
(declare-fun xs () Int)
(declare-fun ql1 () NUM)
(declare-fun xl () NUM)
(declare-fun qs1 () Int)
(declare-fun flted1 () Int)
(declare-fun n () Int)
(declare-fun vprm () Int)
(declare-fun qmin1 () Int)


(assert 
(exists ((sres Int)(lres Int)(nres Int))(and 
;lexvar(<= xs1 xl1)
(<= 0 n1)
(<= nres n1)
(<= n1 (+ nres 1))
(<= lres xl1)
(<= xs1 sres)
(<= qs1 ql1)
(<= 0 flted1)
(= xl1 ql1)
(= xs1 qs1)
(= n1 flted1)
(= tmpprm q1)
(= xprm x)
(= vprm v)
(distinct xprm nil)
(<= xs qmin1)
(<= ql1 xl)
(<= qmin1 qs1)
(= (+ flted1 1) n)
(<= qmin1 vprm)
(distinct vprm qmin1)
(tobool (ssep 
(sll v6prm nres sres lres)
(pto xprm (sref (ref val qmin1) (ref next q1) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val4prm) (ref next next4prm) ))
 )
)
))

(check-sat)