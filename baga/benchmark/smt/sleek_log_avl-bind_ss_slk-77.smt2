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











































































































































































(declare-fun rlm () Int)
(declare-fun rrm () Int)
(declare-fun v30prm () Int)
(declare-fun v31prm () Int)
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun lm () Int)
(declare-fun lprm () node)
(declare-fun l () node)
(declare-fun rlprm () node)
(declare-fun rl () node)
(declare-fun rrprm () node)
(declare-fun rr () node)
(declare-fun flted9 () Int)
(declare-fun ln2 () Int)
(declare-fun ln () Int)
(declare-fun vprm () Int)


(assert 
(and 
;lexvar(= v30prm 1)
(<= 0 n)
(<= 0 m)
(= v31prm n)
(<= 0 ln)
(<= 0 lm)
(= n ln)
(= m lm)
(= lprm l)
(= rlprm rl)
(= rrprm rr)
(= flted9 (+ 1 ln))
(= ln2 ln)
(= vprm 10)
(tobool (ssep 
(avl rl rlm ln2)
(avl rr rrm flted9)
(avl lprm m n)
) )
)
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)