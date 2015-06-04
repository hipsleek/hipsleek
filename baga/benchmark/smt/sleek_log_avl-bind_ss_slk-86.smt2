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











































































































































































(declare-fun llm () Int)
(declare-fun lrm () Int)
(declare-fun tmpprm () node)
(declare-fun v36prm () Int)
(declare-fun hprm () Int)
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun rm () Int)
(declare-fun llprm () node)
(declare-fun ll () node)
(declare-fun lrprm () node)
(declare-fun lr () node)
(declare-fun rprm () node)
(declare-fun r () node)
(declare-fun flted14 () Int)
(declare-fun flted15 () Int)
(declare-fun lln () Int)
(declare-fun vprm () Int)


(assert 
(and 
;lexvar(= v36prm 1)
(= hprm (+ 1 n))
(<= 0 n)
(<= 0 m)
(<= 0 flted15)
(<= 0 rm)
(= n flted15)
(= m rm)
(= llprm ll)
(= lrprm lr)
(= rprm r)
(= (+ flted14 1) lln)
(= (+ flted15 1) lln)
(= vprm 10)
(tobool (ssep 
(avl ll llm lln)
(avl lr lrm flted14)
(avl rprm m n)
(pto tmpprm (sref (ref val vprm) (ref height hprm) (ref left lrprm) (ref right rprm) ))
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