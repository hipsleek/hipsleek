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











































































































































































(declare-fun dm () Int)
(declare-fun tmp1prm () node)
(declare-fun n30 () Int)
(declare-fun m24 () node)
(declare-fun cm () node)
(declare-fun hprm () Int)
(declare-fun h5 () Int)
(declare-fun n29 () Int)
(declare-fun m23 () Int)
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
;lexvar(= n30 cn)
(= m24 cm)
(= hprm (+ 1 h5))
;eqmax(<= 0 n29)
(<= 0 m23)
(<= 0 bn)
(<= 0 bm)
(= n29 bn)
(= m23 bm)
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
(avl bprm m23 n29)
(pto tmp1prm (sref (ref val v3prm) (ref height hprm) (ref left aprm) (ref right bprm) ))
) )
)
)

(assert (not 
;lexvar
))

(check-sat)