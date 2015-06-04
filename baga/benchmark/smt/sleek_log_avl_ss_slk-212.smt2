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

(define-fun avl ((?in node) (?size Int) (?height Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?size 0)
(= ?height 0)

)(exists ((?height_34 Int))(and 
(= ?size (+ (+ ?size2 1) ?size1))
(<= ?height2 (+ 1 ?height1))
(<= ?height1 (+ 1 ?height2))
(= ?height_34 ?height)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref height ?height_34) (ref left ?p) (ref right ?q) ))
(avl ?p ?size1 ?height1)
(avl ?q ?size2 ?height2)
) )
)))))























































































































































































































































































































































































































































(declare-fun v123prm () node)
(declare-fun v124_19192 () Int)
(declare-fun x () node)
(declare-fun aprm () Int)
(declare-fun a () Int)
(declare-fun xprm () node)
(declare-fun tmp1_19194 () node)
(declare-fun tmp1_19193 () node)
(declare-fun res () node)
(declare-fun n () Int)
(declare-fun m () Int)


(assert 
(exists ((v124prm Int)(tmp1prm node))(and 
;lexvar(= res v123prm)
(= v124prm 1)
(= xprm x)
(= aprm a)
(= tmp1prm nil)
(= xprm nil)
(tobool (ssep 
(avl x m n)
(pto v123prm (sref (ref val aprm) (ref height v124prm) (ref left tmp1prm) (ref right tmp1prm) ))
) )
))
)

(assert (not 
(exists ((flted22 Int)(Anon28 Int))(and 
(= flted22 (+ 1 m))
(<= 0 n)
(<= 0 m)
(tobool  
(avl res flted22 Anon28)
 )
))
))

(check-sat)