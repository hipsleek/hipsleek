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
(declare-fun q50 () node)
(declare-fun Anon50 () node)
(declare-fun Anon49 () node)
(declare-fun ys11 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next15 () node)
(declare-fun q49 () node)
(declare-fun xs11 () node)
(declare-fun flted70 () Int)
(declare-fun flted71_3438 () Int)
(declare-fun n18 () Int)
(declare-fun m11 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted71 Int))(and 
;lexvar(= (+ m 1) m11)
(= q50 ys11)
(= Anon50 Anon49)
(= (+ flted70 1) n)
(= ys11 ys)
(= xs11 xs)
(= next15 q49)
(= n18 flted70)
(<= 0 m)
(distinct xs11 nil)
(<= 0 flted70)
(= flted71 (+ m11 n18))
(= xsprm nil)
(<= 0 n18)
(<= 0 m11)
(tobool  
(ll ysprm flted71)
 )
))
)

(assert (not 
(exists ((flted72 Int))(and 
(= xsprm nil)
(= flted72 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted72)
 )
))
))

(check-sat)