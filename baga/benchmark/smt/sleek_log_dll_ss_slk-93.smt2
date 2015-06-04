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








































































































































(declare-fun Anon31 () Int)
(declare-fun Anon33 () Int)
(declare-fun q30 () node2)
(declare-fun Anon29 () Int)
(declare-fun next7 () node2)
(declare-fun prev4 () node2)
(declare-fun q28 () node2)
(declare-fun q26 () node2)
(declare-fun a () Int)
(declare-fun aprm () Int)
(declare-fun xprm () node2)
(declare-fun p27 () node2)
(declare-fun p29 () node2)
(declare-fun self22 () node2)
(declare-fun flted33 () Int)
(declare-fun p31 () node2)
(declare-fun self24 () node2)
(declare-fun flted37 () Int)
(declare-fun flted35 () Int)
(declare-fun self26_3676 () node2)
(declare-fun self26 () node2)
(declare-fun x () node2)
(declare-fun p () node2)
(declare-fun n () Int)


(assert 
(and 
;lexvar(= next7 q26)
(= prev4 p31)
(= self26 q28)
(= self24 q26)
(= xprm x)
(= aprm a)
(< a n)
(< 0 a)
(= aprm 1)
(= self22 xprm)
(= p27 p)
(= (+ flted33 1) n)
(= p29 self22)
(= (+ flted35 1) flted33)
(distinct self26 nil)
(= p31 self24)
(= (+ flted37 1) flted35)
(tobool (ssep 
(pto self24 (sref (ref val Anon31) (ref prev p29) (ref next q28) ))
(dll q30 self26 flted37)
(pto self26 (sref (ref val Anon33) (ref prev xprm) (ref next q30) ))
(pto xprm (sref (ref val Anon29) (ref prev p27) (ref next self26) ))
) )
)
)

(assert (not 
(exists ((p35 node2)(flted40 Int))(and 
(= p35 p)
(= (+ flted40 1) n)
(<= 0 n)
(tobool  
(dll x p35 flted40)
 )
))
))

(check-sat)