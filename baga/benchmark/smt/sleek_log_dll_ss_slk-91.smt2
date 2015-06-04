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








































































































































(declare-fun Anon35 () Int)
(declare-fun v26prm () node2)
(declare-fun q32 () node2)
(declare-fun x () node2)
(declare-fun a () Int)
(declare-fun aprm () Int)
(declare-fun self28 () node2)
(declare-fun xprm () node2)
(declare-fun p33 () node2)
(declare-fun p () node2)
(declare-fun flted39 () Int)
(declare-fun n () Int)
(declare-fun v27prm () Int)


(assert 
(and 
;lexvar(= (+ v27prm 1) aprm)
(= v26prm q32)
(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(distinct aprm 1)
(= self28 xprm)
(= p33 p)
(= (+ flted39 1) n)
(tobool (ssep 
(pto xprm (sref (ref val Anon35) (ref prev p33) (ref next q32) ))
(dll q32 self28 flted39)
) )
)
)

(assert (not 
(and 
(< 0 v27prm)
(< v27prm n5)
(tobool  
(dll v26prm p34 n5)
 )
)
))

(check-sat)