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























































































































































































































































































































































































































































(declare-fun cm () Int)
(declare-fun dm () Int)
(declare-fun tmp1prm () node)
(declare-fun hprm () Int)
(declare-fun h () Int)
(declare-fun n2 () Int)
(declare-fun m2 () Int)
(declare-fun bm () Int)
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun am () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun dprm () node)
(declare-fun d () node)
(declare-fun v1prm () Int)
(declare-fun v1 () Int)
(declare-fun v2prm () node)
(declare-fun v2 () node)
(declare-fun v3prm () node)
(declare-fun v3 () node)
(declare-fun bn () Int)
(declare-fun cn () Int)
(declare-fun an2 () Int)
(declare-fun an () Int)


(assert 
(and 
;lexvar(= hprm (+ 1 h))
;eqmax(<= 0 n2)
(<= 0 m2)
(<= 0 bn)
(<= 0 bm)
(= n2 bn)
(= m2 bm)
(<= 0 n)
(<= 0 m)
(<= 0 an)
(<= 0 am)
(= n an)
(= m am)
(= aprm a)
(= bprm b)
(= cprm c)
(= dprm d)
(= v1prm v1)
(= v2prm v2)
(= v3prm v3)
;eqmax(<= (+ 0 cn) (+ bn 1))
(<= bn (+ 1 cn))
(= an2 an)
(tobool (ssep 
(avl c cm cn)
(avl d dm an2)
(avl aprm m n)
(avl bprm m2 n2)
(pto tmp1prm (sref (ref val v1prm) (ref height hprm) (ref left aprm) (ref right bprm) ))
) )
)
)

(assert (not 
(and 
(tobool  
(avl cprm m3 n3)
 )
)
))

(check-sat)