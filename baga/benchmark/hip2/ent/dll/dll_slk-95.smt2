(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/hip/
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

)(exists ((?p_41 node2)(?self_42 node2)(?flted_12_40 Int))(and 
(= (+ ?flted_12_40 1) ?n)
(= ?p_41 ?p)
(= ?self_42 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref prev ?p_41) (ref next ?q) ))
(dll ?q ?self_42 ?flted_12_40)
) )
)))))








































































































































(declare-fun Anon35 () Int)
(declare-fun q32 () node2)
(declare-fun p33 () node2)
(declare-fun a () Int)
(declare-fun xprm () node2)
(declare-fun v27_3839 () Int)
(declare-fun aprm () Int)
(declare-fun p34 () node2)
(declare-fun self28 () node2)
(declare-fun flted39 () Int)
(declare-fun flted41_3838 () Int)
(declare-fun n5 () Int)
(declare-fun x () node2)
(declare-fun p () node2)
(declare-fun n () Int)


(assert 
(exists ((flted41 Int)(v27prm Int))(and 
;lexvar(= (+ flted39 1) n)
(= p33 p)
(= self28 xprm)
(not )(distinct aprm 1)
(< 0 a)
(< a n)
(= aprm a)
(= xprm x)
(= (+ v27prm 1) aprm)
(= p34 self28)
(= n5 flted39)
(<= 0 flted39)
(= (+ flted41 1) n5)
(<= 0 n5)
(tobool (ssep 
(pto xprm (sref (ref val Anon35) (ref prev p33) (ref next q32) ))
(dll q32 p34 flted41)
) )
))
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