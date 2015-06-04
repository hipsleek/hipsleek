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





































































































































































































































































































































































(declare-fun tmp1_1337 () node)
(declare-fun v19_1336 () Int)
(declare-fun v18_1335 () Int)
(declare-fun v17_1334 () Int)
(declare-fun v16_1333 () Int)
(declare-fun flted40_1330 () Int)
(declare-fun flted41_1331 () Int)
(declare-fun flted42_1332 () Int)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun ha_1338 () Int)
(declare-fun ha_1339 () Int)
(declare-fun res () node)
(declare-fun nc () Int)
(declare-fun nb () Int)
(declare-fun ha () Int)
(declare-fun na () Int)


(assert 
(exists ((flted40 Int)(flted41 Int)(flted42 Int)(v16prm Int)(v17prm Int)(v18prm Int)(v19prm Int)(tmp1prm node))(and 
;lexvar(= v19prm 0)
(= v18prm 0)
(= v17prm 1)
(= v16prm 0)
(= flted40 0)
(= flted41 0)
(= flted42 0)
(= cprm c)
(= bprm b)
(= aprm a)
(tobool (ssep 
(rb a na flted42 ha)
(rb b nb flted41 ha)
(rb c nc flted40 ha)
(pto tmp1prm (sref (ref val v16prm) (ref color v17prm) (ref left bprm) (ref right cprm) ))
(pto res (sref (ref val v18prm) (ref color v19prm) (ref left aprm) (ref right tmp1prm) ))
) )
))
)

(assert (not 
(exists ((flted43 Int)(flted44 Int)(flted45 Int))(and 
(= flted43 (+ 1 ha))
(= flted44 0)
(= flted45 (+ (+ (+ 2 nb) na) nc))
(<= 0 nc)
(<= 0 nb)
(<= 1 ha)
(<= 0 na)
(tobool  
(rb res flted45 flted44 flted43)
 )
))
))

(check-sat)