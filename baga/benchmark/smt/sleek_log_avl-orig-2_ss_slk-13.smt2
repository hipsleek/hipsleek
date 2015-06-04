(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun ele () (Field node Int))
(declare-fun height () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun avl ((?in node) (?m Int) (?n Int) (?bal Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?m 0)
(= ?n 0)
(= ?bal 1)

)(exists ((?n_80 Int))(and 
(= ?m (+ (+ ?m2 1) ?m1))
(<= (+ 0 ?n2) (+ ?n1 1))
(<= ?n1 (+ 1 ?n2))
(= (+ ?bal ?n2) (+ 1 ?n1))
(= ?n_80 ?n)
(tobool (ssep 
(pto ?in (sref (ref ele ?Anon_14) (ref height ?n_80) (ref left ?p) (ref right ?q) ))
(avl ?p ?m1 ?n1 ?Anon_15)
(avl ?q ?m2 ?n2 ?Anon_16)
) )
)))))






































































































































































































































































































































(declare-fun Anon_219 () Int)
(declare-fun p_220 () node)
(declare-fun Anon1_223 () Int)
(declare-fun q_224 () node)
(declare-fun Anon2_227 () Int)
(declare-fun x () node)
(declare-fun xprm () node)
(declare-fun n1_218 () Int)
(declare-fun b () Int)
(declare-fun n () Int)
(declare-fun n2_222 () Int)
(declare-fun n3_226 () Int)
(declare-fun m () Int)
(declare-fun m1_221 () Int)
(declare-fun m2_225 () Int)


(assert 
(exists ((n1 Int)(Anon Int)(p node)(m1 Int)(n2 Int)(Anon1 Int)(q node)(m2 Int)(n3 Int)(Anon2 Int))(and 
;lexvar(= xprm x)
(distinct xprm nil)
(= n1 n)
(= (+ b n3) (+ 1 n2))
(<= n2 (+ 1 n3))
(<= (+ 0 n3) (+ n2 1))
(= m (+ (+ m2 1) m1))
(tobool (ssep 
(pto xprm (sref (ref ele Anon) (ref height n1) (ref left p) (ref right q) ))
(avl p m1 n2 Anon1)
(avl q m2 n3 Anon2)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref ele eleprm) (ref height heightprm) (ref left leftprm) (ref right rightprm) ))
 )
)
))

(check-sat)