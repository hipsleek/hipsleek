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
(declare-fun q44 () node)
(declare-fun Anon44 () node)
(declare-fun Anon43 () node)
(declare-fun ys9 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next13 () node)
(declare-fun q43 () node)
(declare-fun xs9 () node)
(declare-fun flted62 () Int)
(declare-fun flted63_2976 () Int)
(declare-fun n16 () Int)
(declare-fun m9 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted63 Int))(and 
;lexvar(= (+ m 1) m9)
(= q44 ys9)
(= Anon44 Anon43)
(= (+ flted62 1) n)
(= ys9 ys)
(= xs9 xs)
(= next13 q43)
(= n16 flted62)
(<= 0 m)
(distinct xs9 nil)
(<= 0 flted62)
(= flted63 (+ m9 n16))
(= xsprm nil)
(<= 0 n16)
(<= 0 m9)
(tobool  
(ll ysprm flted63)
 )
))
)

(assert (not 
(exists ((flted64 Int))(and 
(= xsprm nil)
(= flted64 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted64)
 )
))
))

(check-sat)