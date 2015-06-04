(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node2 0)
(declare-fun val () (Field node2 Int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?p_40 node2)(?self_41 node2)(?flted_12_39 Int))(and 
(= (+ ?flted_12_39 1) ?n)
(= ?p_40 ?p)
(= ?self_41 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref prev ?p_40) (ref next ?q) ))
(dll ?q ?self_41 ?flted_12_39)
) )
)))))








































































































































(declare-fun Anon39 () Int)
(declare-fun Anon40_4386 () Int)
(declare-fun q40_4387 () node2)
(declare-fun q39 () node2)
(declare-fun p41 () node2)
(declare-fun p () node2)
(declare-fun xprm () node2)
(declare-fun x () node2)
(declare-fun n () Int)
(declare-fun self33_4384 () node2)
(declare-fun tmp1prm () node2)
(declare-fun p42_4383 () node2)
(declare-fun self32 () node2)
(declare-fun flted46_4385 () Int)
(declare-fun flted45 () Int)


(assert 
(exists ((p42 node2)(self33 node2)(flted46 Int)(Anon40 Int)(q40 node2))(and 
;lexvar(= tmp1prm q39)
(= (+ flted45 1) n)
(= p41 p)
(= self32 xprm)
(= xprm x)
(< 1 n)
(= self33 tmp1prm)
(= p42 self32)
(= (+ flted46 1) flted45)
(tobool (ssep 
(pto xprm (sref (ref val Anon39) (ref prev p41) (ref next q39) ))
(pto tmp1prm (sref (ref val Anon40) (ref prev p42) (ref next q40) ))
(dll q40 self33 flted46)
) )
))
)

(assert (not 
(and 
(tobool  
(pto tmp1prm (sref (ref val val30prm) (ref prev prev30prm) (ref next next30prm) ))
 )
)
))

(check-sat)