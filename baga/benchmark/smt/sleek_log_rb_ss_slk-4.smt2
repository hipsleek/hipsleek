(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


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
(declare-fun flted9_377 () Int)
(declare-fun flted8_376 () Int)
(declare-fun flted7_375 () Int)
(declare-fun flted6_374 () Int)
(declare-fun v5_378 () Int)
(declare-fun v6_379 () Int)
(declare-fun bha_380 () Int)
(declare-fun bha_381 () Int)
(declare-fun bha_382 () Int)
(declare-fun bha () Int)


(assert 
(exists ((flted6 Int)(flted7 Int)(flted8 Int)(flted9 Int)(v5prm Int)(v6prm Int))(and 
;lexvar(= aprm a)
(= bprm b)
(= cprm c)
(= dprm d)
(= flted9 0)
(= flted8 0)
(= flted7 0)
(= flted6 0)
(= v5prm 0)
(= v6prm 1)
(tobool (ssep 
(rb a na flted9 bha)
(rb b nb flted8 bha)
(rb c nc flted7 bha)
(rb d nd flted6 bha)
(pto tmpprm (sref (ref val v5prm) (ref color v6prm) (ref left aprm) (ref right bprm) ))
) )
))
)

(assert (not 
(exists ((bha2 Int)(bha3 Int)(flted Int)(flted1 Int)(flted2 Int))(and 
(= bha3 bha1)
(= bha2 bha1)
(= flted 0)
(= flted1 0)
(= flted2 1)
(tobool (ssep 
(rb tmpprm na1 flted2 bha1)
(rb cprm nb1 flted1 bha2)
(rb dprm nc1 flted bha3)
) )
))
))

(check-sat)