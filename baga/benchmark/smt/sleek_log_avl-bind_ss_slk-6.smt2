(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun height () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun avl ((?in node) (?m Int) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?m 0)
(= ?n 0)

)(exists ((?n_33 Int))(and 
(= ?m (+ (+ ?m2 1) ?m1))
(<= (+ 0 ?n2) (+ ?n1 1))
(<= ?n1 (+ 1 ?n2))
(= ?n_33 ?n)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref height ?n_33) (ref left ?p) (ref right ?q) ))
(avl ?p ?m1 ?n1)
(avl ?q ?m2 ?n2)
) )
)))))











































































































































































(declare-fun Anon1 () Int)
(declare-fun p1 () node)
(declare-fun q1 () node)
(declare-fun v_231 () Int)
(declare-fun nx2 () Int)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun n5 () Int)
(declare-fun n4 () Int)
(declare-fun m4 () Int)
(declare-fun m3 () Int)
(declare-fun n6 () Int)
(declare-fun tmp_232 () Int)
(declare-fun tmp () Int)
(declare-fun v2prm () node)
(declare-fun res () node)
(declare-fun my () Int)
(declare-fun nx () Int)
(declare-fun mx () Int)


(assert 
(exists ((vprm Int)(tmpprm Int))(and 
;lexvar(= vprm 0)
(= nx2 nx)
(distinct x nil)
(= yprm y)
(= xprm x)
(= n6 nx)
(<= n4 (+ 1 n5))
(<= (+ 0 n5) (+ n4 1))
(= mx (+ (+ m3 1) m4))
(= tmp n6)
(= tmpprm (+ 1 tmp))
(= res v2prm)
(tobool (ssep 
(pto xprm (sref (ref val Anon1) (ref height n6) (ref left p1) (ref right q1) ))
(avl p1 m4 n4)
(avl q1 m3 n5)
(avl y my nx2)
(pto v2prm (sref (ref val vprm) (ref height tmpprm) (ref left xprm) (ref right yprm) ))
) )
))
)

(assert (not 
(exists ((flted Int)(flted1 Int))(and 
(= flted (+ nx 1))
(= flted1 (+ (+ my 1) mx))
(<= 0 my)
(<= 0 nx)
(<= 0 mx)
(tobool  
(avl res flted1 flted)
 )
))
))

(check-sat)