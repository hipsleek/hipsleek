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

(define-fun bndl ((?in node) (?n Int) (?sm NUM) (?bg Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)
(<= ?sm ?bg)

)(exists ((?sm_23 Int)(?bg_24 Int)(?flted_11_22 Int))(and 
(= (+ ?flted_11_22 1) ?n)
(<= ?sm ?d)
(<= ?d ?bg)
(= ?sm_23 ?sm)
(= ?bg_24 ?bg)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref next ?p) ))
(bndl ?p ?flted_11_22 ?sm_23 ?bg_24)
) )
)))))






(declare-fun p_83 () node)
(declare-fun flted_81 () Int)
(declare-fun n () Int)
(declare-fun d_82 () Int)
(declare-fun sm1_79 () Int)
(declare-fun sm () Int)
(declare-fun bg1_80 () Int)
(declare-fun bg () Int)
(declare-fun xprm () node)
(declare-fun x () node)


(assert 
(exists ((sm1 Int)(bg1 Int)(flted Int)(d Int)(p node))(and 
;lexvar(= (+ flted 1) n)
(<= sm d)
(<= d bg)
(= sm1 sm)
(= bg1 bg)
(= xprm x)
(distinct x nil)
(tobool (ssep 
(bndl p flted sm1 bg1)
(pto xprm (sref (ref val d) (ref next p) ))
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