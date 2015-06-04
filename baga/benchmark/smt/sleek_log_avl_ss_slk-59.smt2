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























































































































































































































































































































































































































































(declare-fun dm () Int)
(declare-fun tmp1prm () node)
(declare-fun n8 () Int)
(declare-fun m8 () node)
(declare-fun cm () node)
(declare-fun hprm () Int)
(declare-fun h5 () Int)
(declare-fun n7 () Int)
(declare-fun m7 () Int)
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
(declare-fun v1prm () node)
(declare-fun v1 () node)
(declare-fun v2prm () node)
(declare-fun v2 () node)
(declare-fun v3prm () Int)
(declare-fun v3 () Int)
(declare-fun cn () Int)
(declare-fun bn () Int)
(declare-fun an4 () Int)
(declare-fun an () Int)


(assert 
(and 
;lexvar(= n8 cn)
(= m8 cm)
(= hprm (+ 1 h5))
;eqmax(<= 0 n7)
(<= 0 m7)
(<= 0 bn)
(<= 0 bm)
(= n7 bn)
(= m7 bm)
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
;eqmax(<= (+ 0 bn) (+ cn 1))
(<= cn (+ 1 bn))
(= an4 an)
(tobool (ssep 
(avl d dm an4)
(avl aprm m n)
(avl bprm m7 n7)
(pto tmp1prm (sref (ref val v3prm) (ref height hprm) (ref left aprm) (ref right bprm) ))
) )
)
)

(assert (not 
;lexvar
))

(check-sat)