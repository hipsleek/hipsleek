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























































































































































































































































































































































































































































(declare-fun Anon25 () Int)
(declare-fun p17 () node)
(declare-fun Anon27 () Int)
(declare-fun v5 () node)
(declare-fun v119prm () Int)
(declare-fun v120prm () Int)
(declare-fun v121prm () Int)
(declare-fun v122prm () node)
(declare-fun q17 () node)
(declare-fun v117prm () node)
(declare-fun q19 () node)
(declare-fun v114prm () node)
(declare-fun p19 () node)
(declare-fun v111prm () node)
(declare-fun p11 () node)
(declare-fun m25 () Int)
(declare-fun n25 () Int)
(declare-fun m23 () Int)
(declare-fun m22 () Int)
(declare-fun n21 () Int)
(declare-fun m21 () Int)
(declare-fun Anon23 () Int)
(declare-fun right1 () node)
(declare-fun flted21 () Int)
(declare-fun n19 () Int)
(declare-fun m19 () Int)
(declare-fun tmpprm () node)
(declare-fun q11 () node)
(declare-fun x () node)
(declare-fun a () Int)
(declare-fun tmp1prm () node)
(declare-fun xprm () node)
(declare-fun height33 () Int)
(declare-fun n () Int)
(declare-fun height32 () Int)
(declare-fun height31 () Int)
(declare-fun m () Int)
(declare-fun size24 () Int)
(declare-fun size23 () Int)
(declare-fun Anon15 () Int)
(declare-fun aprm () Int)
(declare-fun height49 () Int)
(declare-fun n20 () Int)
(declare-fun height50 () Int)
(declare-fun height51 () Int)
(declare-fun m20 () Int)
(declare-fun size36 () Int)
(declare-fun size35 () Int)
(declare-fun n22 () Int)
(declare-fun n23 () Int)
(declare-fun height55 () Int)
(declare-fun n24 () Int)
(declare-fun height56 () Int)
(declare-fun height57 () Int)
(declare-fun m24 () Int)
(declare-fun size40 () Int)
(declare-fun size39 () Int)


(assert 
(and 
;lexvar(= v119prm 1)
(= v120prm 1)
(= v121prm 1)
(= v122prm q17)
(= v117prm q19)
(= v114prm p19)
(= v111prm p11)
(<= 0 n25)
(<= 0 m25)
(<= 0 n22)
(<= 0 m22)
(= n25 n22)
(= m25 m22)
(= (+ n25 1) n24)
(<= 0 n24)
(<= 0 m24)
(<= 0 n23)
(<= 0 m23)
(= n24 n23)
(= m24 m23)
(<= 0 height51)
(<= 0 size36)
(= n23 height51)
(= m23 size36)
(<= 0 height50)
(<= 0 size35)
(= n22 height50)
(= m22 size35)
(= (+ 2 n21) n20)
(<= 0 n21)
(<= 0 m21)
(<= 0 height31)
(<= 0 size24)
(= n21 height31)
(= m21 size24)
(<= 0 n20)
(<= 0 m20)
(<= 0 Anon23)
(<= 0 flted21)
(= n20 Anon23)
(= m20 flted21)
(= right1 q11)
(<= 0 n19)
(<= 0 m19)
(= flted21 (+ 1 m19))
(<= 0 height32)
(<= 0 size23)
(= n19 height32)
(= m19 size23)
(= tmpprm q11)
(= xprm x)
(= aprm a)
(= tmp1prm nil)
(distinct xprm nil)
(= height33 n)
(<= height31 (+ 1 height32))
(<= height32 (+ 1 height31))
(= m (+ (+ size23 1) size24))
(< Anon15 aprm)
(= height49 n20)
(<= height51 (+ 1 height50))
(<= height50 (+ 1 height51))
(= m20 (+ (+ size35 1) size36))
(<= n22 n23)
(= height55 n24)
(<= height57 (+ 1 height56))
(<= height56 (+ 1 height57))
(= m24 (+ (+ size39 1) size40))
(tobool (ssep 
(pto v5 (sref (ref val Anon25) (ref height height49) (ref left p17) (ref right q17) ))
(pto p17 (sref (ref val Anon27) (ref height height55) (ref left p19) (ref right q19) ))
(avl q17 m25 n25)
(pto xprm (sref (ref val Anon15) (ref height height33) (ref left p11) (ref right v5) ))
(avl p11 m21 n21)
(avl p19 size40 height57)
(avl q19 size39 height56)
) )
)
)

(assert (not 
(exists ((an3 Int))(and 
(= an3 an)
(<= cn (+ 1 bn))
(<= (+ 0 bn) (+ cn 1))
;eqmax(tobool (ssep 
(avl v111prm am an)
(avl v114prm bm bn)
(avl v117prm cm cn)
(avl v122prm dm an3)
) )
))
))

(check-sat)