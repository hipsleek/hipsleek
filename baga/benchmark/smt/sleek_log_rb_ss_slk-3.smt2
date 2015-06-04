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





































































































































































































































































































































































(declare-fun tmp_162 () node)
(declare-fun vprm () node)
(declare-fun v4_161 () Int)
(declare-fun v3_160 () Int)
(declare-fun v2_159 () Int)
(declare-fun v1_158 () Int)
(declare-fun flted_155 () Int)
(declare-fun flted1_156 () Int)
(declare-fun flted2_157 () Int)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bha_163 () Int)
(declare-fun bha_164 () Int)
(declare-fun res () node)
(declare-fun nc () Int)
(declare-fun nb () Int)
(declare-fun bha () Int)
(declare-fun na () Int)


(assert 
(exists ((flted Int)(flted1 Int)(flted2 Int)(v1prm Int)(v2prm Int)(v3prm Int)(v4prm Int)(tmpprm node))(and 
;lexvar(= res vprm)
(= v4prm 0)
(= v3prm 0)
(= v2prm 1)
(= v1prm 0)
(= flted 0)
(= flted1 0)
(= flted2 1)
(= cprm c)
(= bprm b)
(= aprm a)
(tobool (ssep 
(rb a na flted2 bha)
(rb b nb flted1 bha)
(rb c nc flted bha)
(pto tmpprm (sref (ref val v1prm) (ref color v2prm) (ref left bprm) (ref right cprm) ))
(pto vprm (sref (ref val v3prm) (ref color v4prm) (ref left aprm) (ref right tmpprm) ))
) )
))
)

(assert (not 
(exists ((flted3 Int)(flted4 Int)(flted5 Int))(and 
(= flted3 (+ 1 bha))
(= flted4 0)
(= flted5 (+ (+ (+ 2 nb) na) nc))
(<= 0 nc)
(<= 0 nb)
(<= 1 bha)
(<= 0 na)
(tobool  
(rb res flted5 flted4 flted3)
 )
))
))

(check-sat)