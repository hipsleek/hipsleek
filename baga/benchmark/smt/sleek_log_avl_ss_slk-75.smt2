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























































































































































































































































































































































































































































(declare-fun lm () Int)
(declare-fun rlm () Int)
(declare-fun rrm () Int)
(declare-fun lprm () node)
(declare-fun l () node)
(declare-fun rlprm () node)
(declare-fun rl () node)
(declare-fun rrprm () node)
(declare-fun rr () node)
(declare-fun flted8_5646 () Int)
(declare-fun ln1_5645 () Int)
(declare-fun ln () Int)
(declare-fun vprm () Int)


(assert 
(exists ((ln1 Int)(flted8 Int))(and 
;lexvar(= lprm l)
(= rlprm rl)
(= rrprm rr)
(= flted8 (+ 1 ln))
(= ln1 ln)
(= vprm 10)
(tobool (ssep 
(avl l lm ln)
(avl rl rlm ln1)
(avl rr rrm flted8)
) )
))
)

(assert (not 
(and 
(tobool  
(avl lprm m n)
 )
)
))

(check-sat)