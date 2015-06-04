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
(declare-fun flted29_964 () Int)
(declare-fun flted28_963 () Int)
(declare-fun flted27_962 () Int)
(declare-fun flted26_961 () Int)
(declare-fun v13_965 () Int)
(declare-fun v14_966 () Int)
(declare-fun bha_967 () Int)
(declare-fun bha_968 () Int)
(declare-fun bha_969 () Int)
(declare-fun bha () Int)


(assert 
(exists ((flted26 Int)(flted27 Int)(flted28 Int)(flted29 Int)(v13prm Int)(v14prm Int))(and 
;lexvar(= aprm a)
(= bprm b)
(= cprm c)
(= dprm d)
(= flted29 0)
(= flted28 0)
(= flted27 0)
(= flted26 0)
(= v13prm 0)
(= v14prm 1)
(tobool (ssep 
(rb a na flted29 bha)
(rb b nb flted28 bha)
(rb c nc flted27 bha)
(rb d nd flted26 bha)
(pto tmpprm (sref (ref val v13prm) (ref color v14prm) (ref left cprm) (ref right dprm) ))
) )
))
)

(assert (not 
(exists ((bha5 Int)(bha6 Int)(flted20 Int)(flted21 Int)(flted22 Int))(and 
(= bha6 bha4)
(= bha5 bha4)
(= flted20 1)
(= flted21 0)
(= flted22 0)
(tobool (ssep 
(rb aprm na2 flted22 bha4)
(rb bprm nb2 flted21 bha5)
(rb tmpprm nc2 flted20 bha6)
) )
))
))

(check-sat)