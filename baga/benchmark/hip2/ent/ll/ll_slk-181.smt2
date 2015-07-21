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
(declare-fun q62 () node)
(declare-fun Anon62 () node)
(declare-fun Anon61 () node)
(declare-fun ys15 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next19 () node)
(declare-fun q61 () node)
(declare-fun xs15 () node)
(declare-fun flted86 () Int)
(declare-fun flted87_4362 () Int)
(declare-fun n22 () Int)
(declare-fun m15 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted87 Int))(and 
;lexvar(= (+ m 1) m15)
(= q62 ys15)
(= Anon62 Anon61)
(= (+ flted86 1) n)
(= ys15 ys)
(= xs15 xs)
(= next19 q61)
(= n22 flted86)
(<= 0 m)
(distinct xs15 nil)
(<= 0 flted86)
(= flted87 (+ m15 n22))
(= xsprm nil)
(<= 0 n22)
(<= 0 m15)
(tobool  
(ll ysprm flted87)
 )
))
)

(assert (not 
(exists ((flted88 Int))(and 
(= xsprm nil)
(= flted88 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted88)
 )
))
))

(check-sat)