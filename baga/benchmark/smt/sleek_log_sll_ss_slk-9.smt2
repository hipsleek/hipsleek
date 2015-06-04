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










































































(declare-fun q_162 () node)
(declare-fun x () node)
(declare-fun vprm () node)
(declare-fun v () node)
(declare-fun xprm () node)
(declare-fun xs () Int)
(declare-fun ql_160 () Int)
(declare-fun xl () Int)
(declare-fun qmin_161 () Int)
(declare-fun qs_159 () Int)
(declare-fun flted_158 () Int)
(declare-fun n () Int)


(assert 
(exists ((flted Int)(qs Int)(ql Int)(qmin Int)(q node))(and 
;lexvar(= xprm x)
(= vprm v)
(distinct xprm nil)
(<= xs qmin)
(<= ql xl)
(<= qmin qs)
(= (+ flted 1) n)
(tobool (ssep 
(sll q flted qs ql)
(pto xprm (sref (ref val qmin) (ref next q) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val valprm) (ref next nextprm) ))
 )
)
))

(check-sat)