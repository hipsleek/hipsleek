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











































































































































































(declare-fun my () Int)
(declare-fun mz () Int)
(declare-fun Anon2 () Int)
(declare-fun Anon3 () Int)
(declare-fun Anon4 () node)
(declare-fun Anon5 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun yprm () node)
(declare-fun zprm () node)
(declare-fun z () node)
(declare-fun y () node)
(declare-fun ny1_370 () Int)
(declare-fun ny () Int)


(assert 
(exists ((ny1 Int))(and 
;lexvar(= xprm x)
(= yprm y)
(= zprm z)
(distinct y nil)
(= ny1 ny)
(tobool (ssep 
(avl y my ny)
(avl z mz ny1)
(pto x (sref (ref val Anon2) (ref height Anon3) (ref left Anon4) (ref right Anon5) ))
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val1prm) (ref height height1prm) (ref left left1prm) (ref right right1prm) ))
 )
)
))

(check-sat)