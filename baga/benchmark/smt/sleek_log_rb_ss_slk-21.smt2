(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun color () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun rb ((?in node) (?n Int) (?cl Int) (?bh Int))
Space (tospace
(or
(or
(and 
(= ?in nil)
(= ?n 0)
(= ?bh 1)
(= ?cl 0)

)(exists ((?flted_12_38 Int)(?flted_12_39 Int)(?flted_12_40 Int))(and 
(= ?flted_12_40 1)
(= ?flted_12_39 0)
(= ?flted_12_38 0)
(= ?cl 1)
(= ?n (+ (+ ?nr 1) ?nl))
(= ?bhl ?bh)
(= ?bhr ?bh)
(tobool (ssep 
(pto ?in (sref (ref val ?v) (ref color ?flted_12_40) (ref left ?l) (ref right ?r) ))
(rb ?l ?nl ?flted_12_39 ?bhl)
(rb ?r ?nr ?flted_12_38 ?bhr)
) )
)))(exists ((?flted_13_41 Int))(and 
(= ?flted_13_41 0)
(= ?cl 0)
(= ?n (+ (+ ?nr 1) ?nl))
(= ?bhl ?bhr)
(= ?bh (+ ?bhl 1))
(tobool (ssep 
(pto ?in (sref (ref val ?v) (ref color ?flted_13_41) (ref left ?l) (ref right ?r) ))
(rb ?l ?nl ?Anon_14 ?bhl)
(rb ?r ?nr ?Anon_15 ?bhr)
) )
)))))





































































































































































































































































































































































(declare-fun na () Int)
(declare-fun nb () Int)
(declare-fun nc () Int)
(declare-fun nd () Int)
(declare-fun tmpprm () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun dprm () node)
(declare-fun d () node)
(declare-fun flted87_3593 () Int)
(declare-fun flted86_3592 () Int)
(declare-fun flted85_3591 () Int)
(declare-fun flted84_3590 () Int)
(declare-fun color () Int)
(declare-fun v25_3594 () Int)
(declare-fun v26_3595 () Int)
(declare-fun h_3596 () Int)
(declare-fun h_3597 () Int)
(declare-fun h_3598 () Int)
(declare-fun h () Int)
(declare-fun colorprm () Int)


(assert 
(exists ((flted84 Int)(flted85 Int)(flted86 Int)(flted87 Int)(v25prm Int)(v26prm Int))(and 
;lexvar(= aprm a)
(= bprm b)
(= cprm c)
(= dprm d)
(= colorprm color)
(= flted87 0)
(= flted86 0)
(= flted85 0)
(= flted84 0)
(= color 1)
(= v25prm 0)
(= v26prm 1)
(tobool (ssep 
(rb a na flted87 h)
(rb b nb flted86 h)
(rb c nc flted85 h)
(rb d nd flted84 h)
(pto tmpprm (sref (ref val v25prm) (ref color v26prm) (ref left cprm) (ref right dprm) ))
) )
))
)

(assert (not 
(exists ((h10 Int)(h11 Int)(flted76 Int)(flted77 Int))(and 
(= h11 h9)
(= h10 h9)
(= colorprm 0)
(= flted76 1)
(= flted77 0)
(tobool (ssep 
(rb aprm na3 flted77 h9)
(rb bprm nb3 Anon h10)
(rb tmpprm nc3 flted76 h11)
) )
))
))

(check-sat)