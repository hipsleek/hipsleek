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























































































































































































































































































































































































































































(declare-fun llm () Int)
(declare-fun lrm () Int)
(declare-fun v34prm () Int)
(declare-fun v35prm () Int)
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
;lexvar(= v34prm 1)
(<= 0 n)
(<= 0 m)
(= v35prm n)
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