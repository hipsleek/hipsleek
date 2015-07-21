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
(declare-fun q41 () node)
(declare-fun Anon41 () node)
(declare-fun Anon40 () node)
(declare-fun ys8 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next12 () node)
(declare-fun q40 () node)
(declare-fun xs8 () node)
(declare-fun flted58 () Int)
(declare-fun flted59_2745 () Int)
(declare-fun n15 () Int)
(declare-fun m8 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted59 Int))(and 
;lexvar(= (+ m 1) m8)
(= q41 ys8)
(= Anon41 Anon40)
(= (+ flted58 1) n)
(= ys8 ys)
(= xs8 xs)
(= next12 q40)
(= n15 flted58)
(<= 0 m)
(distinct xs8 nil)
(<= 0 flted58)
(= flted59 (+ m8 n15))
(= xsprm nil)
(<= 0 n15)
(<= 0 m8)
(tobool  
(ll ysprm flted59)
 )
))
)

(assert (not 
(exists ((flted60 Int))(and 
(= xsprm nil)
(= flted60 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted60)
 )
))
))

(check-sat)