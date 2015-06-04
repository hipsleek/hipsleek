(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
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

)(exists ((?flted_14_23 Int))(and 
(= (+ ?flted_14_23 1) ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?q) ))
(ll ?q ?flted_14_23)
) )
)))))
















































































































































































































































(declare-fun ysprm () node)
(declare-fun q35 () node)
(declare-fun Anon35 () node)
(declare-fun Anon34 () node)
(declare-fun ys6 () node)
(declare-fun ys () node)
(declare-fun xs () node)
(declare-fun next10 () node)
(declare-fun q34 () node)
(declare-fun xs6 () node)
(declare-fun flted50 () Int)
(declare-fun flted51_2797 () Int)
(declare-fun n13 () Int)
(declare-fun m6 () Int)
(declare-fun xsprm () node)
(declare-fun m () Int)
(declare-fun n () Int)


(assert 
(exists ((flted51 Int))(and 
;lexvar(= (+ m 1) m6)
(= q35 ys6)
(= Anon35 Anon34)
(= (+ flted50 1) n)
(= ys6 ys)
(= xs6 xs)
(= next10 q34)
(= n13 flted50)
(<= 0 m)
(distinct xs6 nil)
(<= 0 flted50)
(= flted51 (+ m6 n13))
(= xsprm nil)
(<= 0 n13)
(<= 0 m6)
(tobool  
(ll ysprm flted51)
 )
))
)

(assert (not 
(exists ((flted52 Int))(and 
(= xsprm nil)
(= flted52 (+ m n))
(<= 0 m)
(<= 0 n)
(tobool  
(ll ysprm flted52)
 )
))
))

(check-sat)