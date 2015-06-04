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








































































































































(declare-fun Anon27 () Int)
(declare-fun v18prm () Int)
(declare-fun v19prm () node2)
(declare-fun q24 () node2)
(declare-fun x () node2)
(declare-fun a () Int)
(declare-fun tmp1prm () node2)
(declare-fun aprm () Int)
(declare-fun self20 () node2)
(declare-fun xprm () node2)
(declare-fun p23 () node2)
(declare-fun p () node2)
(declare-fun flted29 () Int)
(declare-fun n () NUM)


(assert 
(and 
;lexvar(= v18prm 1)
(= v19prm q24)
(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(= tmp1prm nil)
(distinct aprm 1)
(= self20 xprm)
(= p23 p)
(= (+ flted29 1) n)
(tobool (ssep 
(pto xprm (sref (ref val Anon27) (ref prev p23) (ref next q24) ))
(dll q24 self20 flted29)
) )
)
)

(assert (not 
;lexvar
))

(check-sat)