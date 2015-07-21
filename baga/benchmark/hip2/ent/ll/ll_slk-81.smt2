(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/hip/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun ll ((?in node) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?flted_14_24 Int))(and 
(= (+ ?flted_14_24 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref next ?q) ))
(ll ?q ?flted_14_24)
) )
)))))


















































































































































































































(declare-fun ysprm () node)
(declare-fun q32 () node)
(declare-fun Anon32 () node)
(declare-fun Anon31 () node)
(declare-fun ys5 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next9 () node)
(declare-fun q31 () node)
(declare-fun xs5 () node)
(declare-fun flted46 () Int)
(declare-fun flted47_2052 () Int)
(declare-fun n12 () Int)
(declare-fun m5 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted47 Int))(and 
;lexvar(= (+ m 1) m5)
(= q32 ys5)
(= Anon32 Anon31)
(= (+ flted46 1) n)
(= ys5 ys)
(= xs5 xs)
(= next9 q31)
(= n12 flted46)
(<= 0 m)
(distinct xs5 nil)
(<= 0 flted46)
(= flted47 (+ m5 n12))
(= xsprm nil)
(<= 0 n12)
(<= 0 m5)
(tobool  
(ll ysprm flted47)
 )
))
)

(assert (not 
(exists ((flted48 Int))(and 
(= xsprm nil)
(= flted48 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted48)
 )
))
))

(check-sat)