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























































































































































































































































































































































































































































(declare-fun tmp_5845 () node)
(declare-fun ln2 () Int)
(declare-fun flted9 () Int)
(declare-fun rrprm () node)
(declare-fun rr () node)
(declare-fun rlprm () node)
(declare-fun rl () node)
(declare-fun lprm () node)
(declare-fun l () node)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun h_5846 () Int)
(declare-fun h10 () Int)
(declare-fun v33prm () node)
(declare-fun v_5847 () Int)
(declare-fun v_5844 () Int)
(declare-fun res () node)
(declare-fun rrm () Int)
(declare-fun rlm () Int)
(declare-fun ln () Int)
(declare-fun lm () Int)


(assert 
(exists ((vprm Int)(tmpprm node)(hprm Int))(and 
;lexvar(= vprm 10)
(= ln2 ln)
(= flted9 (+ 1 ln))
(= rrprm rr)
(= rlprm rl)
(= lprm l)
(= m lm)
(= n ln)
(<= 0 lm)
(<= 0 ln)
(<= 0 m)
(<= 0 n)
(= h10 (+ 1 n))
(= hprm (+ 1 h10))
(= res v33prm)
(tobool (ssep 
(avl rl rlm ln2)
(avl rr rrm flted9)
(avl lprm m n)
(pto tmpprm (sref (ref val vprm) (ref height h10) (ref left lprm) (ref right rlprm) ))
(pto v33prm (sref (ref val vprm) (ref height hprm) (ref left tmpprm) (ref right rrprm) ))
) )
))
)

(assert (not 
(exists ((flted10 Int)(flted11 Int))(and 
(= flted10 (+ ln 2))
(= flted11 (+ (+ (+ rrm lm) 2) rlm))
(<= 0 rrm)
(<= 0 rlm)
(<= 0 ln)
(<= 0 lm)
(tobool  
(avl res flted11 flted10)
 )
))
))

(check-sat)