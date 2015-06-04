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











































































































































































(declare-fun tmp_6210 () node)
(declare-fun flted14 () Int)
(declare-fun rprm () node)
(declare-fun r () node)
(declare-fun lrprm () node)
(declare-fun lr () node)
(declare-fun llprm () node)
(declare-fun ll () node)
(declare-fun flted15 () Int)
(declare-fun m () Int)
(declare-fun n () Int)
(declare-fun h_6211 () Int)
(declare-fun h11 () Int)
(declare-fun v37prm () node)
(declare-fun v_6212 () Int)
(declare-fun v_6209 () Int)
(declare-fun res () node)
(declare-fun rm () Int)
(declare-fun lrm () Int)
(declare-fun lln () Int)
(declare-fun llm () Int)


(assert 
(exists ((vprm Int)(tmpprm node)(hprm Int))(and 
;lexvar(= vprm 10)
(= (+ flted15 1) lln)
(= (+ flted14 1) lln)
(= rprm r)
(= lrprm lr)
(= llprm ll)
(= m rm)
(= n flted15)
(<= 0 rm)
(<= 0 flted15)
(<= 0 m)
(<= 0 n)
(= h11 (+ 1 n))
(= hprm (+ 1 h11))
(= res v37prm)
(tobool (ssep 
(avl ll llm lln)
(avl lr lrm flted14)
(avl rprm m n)
(pto tmpprm (sref (ref val vprm) (ref height h11) (ref left lrprm) (ref right rprm) ))
(pto v37prm (sref (ref val vprm) (ref height hprm) (ref left llprm) (ref right tmpprm) ))
) )
))
)

(assert (not 
(exists ((flted16 Int)(flted17 Int))(and 
(= flted16 (+ lln 1))
(= flted17 (+ (+ (+ rm llm) 2) lrm))
(<= 0 rm)
(<= 0 lrm)
(<= 0 lln)
(<= 0 llm)
(tobool  
(avl res flted17 flted16)
 )
))
))

(check-sat)