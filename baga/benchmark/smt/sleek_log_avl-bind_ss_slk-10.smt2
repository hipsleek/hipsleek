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











































































































































































(declare-fun Anon7 () Int)
(declare-fun p3 () node)
(declare-fun q3 () node)
(declare-fun mz () Int)
(declare-fun Anon2 () Int)
(declare-fun Anon3 () Int)
(declare-fun v3prm () Int)
(declare-fun v4prm () Int)
(declare-fun right () node)
(declare-fun Anon5 () node)
(declare-fun left () node)
(declare-fun Anon4 () node)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun yprm () node)
(declare-fun zprm () node)
(declare-fun z () node)
(declare-fun y () node)
(declare-fun ny2 () Int)
(declare-fun n10 () Int)
(declare-fun ny () Int)
(declare-fun n11 () Int)
(declare-fun n12 () Int)
(declare-fun my () Int)
(declare-fun m8 () Int)
(declare-fun m7 () Int)


(assert 
(and 
;lexvar(= v3prm 1)
(= v4prm n10)
(= right Anon5)
(= left Anon4)
(= xprm x)
(= yprm y)
(= zprm z)
(distinct y nil)
(= ny2 ny)
(= n10 ny)
(<= n12 (+ 1 n11))
(<= (+ 0 n11) (+ n12 1))
(= my (+ (+ m7 1) m8))
(tobool (ssep 
(pto yprm (sref (ref val Anon7) (ref height n10) (ref left p3) (ref right q3) ))
(avl p3 m8 n12)
(avl q3 m7 n11)
(avl z mz ny2)
(pto xprm (sref (ref val Anon2) (ref height Anon3) (ref left yprm) (ref right zprm) ))
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