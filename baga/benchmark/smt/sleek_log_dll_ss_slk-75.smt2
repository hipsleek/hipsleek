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








































































































































(declare-fun Anon23 () Int)
(declare-fun Anon21 () Int)
(declare-fun next6 () node2)
(declare-fun self16 () node2)
(declare-fun q18 () node2)
(declare-fun a () Int)
(declare-fun tmp1_2979 () node2)
(declare-fun aprm () Int)
(declare-fun xprm () node2)
(declare-fun p17 () node2)
(declare-fun p19 () node2)
(declare-fun self14 () node2)
(declare-fun flted25 () Int)
(declare-fun flted23 () Int)
(declare-fun q20 () node2)
(declare-fun x () node2)
(declare-fun p () node2)
(declare-fun n () Int)


(assert 
(exists ((tmp1prm node2))(and 
;lexvar(= next6 q18)
(= self16 q18)
(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(= tmp1prm nil)
(= aprm 1)
(= self14 xprm)
(= p17 p)
(= (+ flted23 1) n)
(= p19 self14)
(= (+ flted25 1) flted23)
(= q20 nil)
(tobool (ssep 
(pto self16 (sref (ref val Anon23) (ref prev p19) (ref next q20) ))
(dll q20 self16 flted25)
(pto xprm (sref (ref val Anon21) (ref prev p17) (ref next tmp1prm) ))
) )
))
)

(assert (not 
(exists ((p25 node2)(flted30 Int))(and 
(= p25 p)
(= (+ flted30 1) n)
(<= 0 n)
(tobool  
(dll x p25 flted30)
 )
))
))

(check-sat)