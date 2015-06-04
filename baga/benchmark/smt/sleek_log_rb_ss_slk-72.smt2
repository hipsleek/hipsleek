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





































































































































































































































































































































































(declare-fun v26 () Int)
(declare-fun l18 () node)
(declare-fun r18 () node)
(declare-fun tmp_10287 () node)
(declare-fun v59prm () node)
(declare-fun v62_10286 () Int)
(declare-fun v61_10285 () Int)
(declare-fun v60_10284 () Int)
(declare-fun color3 () Int)
(declare-fun flted158 () Int)
(declare-fun flted159 () Int)
(declare-fun flted160 () Int)
(declare-fun flted161 () Int)
(declare-fun nl18 () Int)
(declare-fun nr18 () Int)
(declare-fun bhl18 () Int)
(declare-fun bhr18 () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun colorprm () Int)
(declare-fun flted162 () Int)
(declare-fun ha7 () Int)
(declare-fun ha8 () Int)
(declare-fun v58_10283 () Int)
(declare-fun res () node)
(declare-fun color () Int)
(declare-fun Anon10 () Int)
(declare-fun na () Int)
(declare-fun ha () Int)
(declare-fun nb () Int)
(declare-fun Anon11 () Int)
(declare-fun nc () Int)


(assert 
(exists ((v58prm Int)(v60prm Int)(v61prm Int)(v62prm Int)(tmpprm node))(and 
;lexvar(= res v59prm)
(= v62prm 0)
(= v61prm 0)
(= v60prm 0)
(= color3 flted158)
(= flted158 1)
(= flted159 0)
(= flted160 0)
(= flted161 1)
(= na (+ (+ nr18 1) nl18))
(= bhl18 ha)
(= bhr18 ha)
(= aprm a)
(= bprm b)
(= cprm c)
(= colorprm color)
(= flted162 0)
(= color 0)
(= ha7 ha)
(= ha8 ha)
(= v58prm 0)
(tobool (ssep 
(rb l18 nl18 flted159 bhl18)
(rb r18 nr18 flted160 bhr18)
(rb b nb Anon10 ha7)
(rb c nc flted162 ha8)
(pto aprm (sref (ref val v26) (ref color v58prm) (ref left l18) (ref right r18) ))
(pto tmpprm (sref (ref val v60prm) (ref color v61prm) (ref left bprm) (ref right cprm) ))
(pto v59prm (sref (ref val v62prm) (ref color colorprm) (ref left aprm) (ref right tmpprm) ))
) )
))
)

(assert (not 
(exists ((flted166 Int)(flted167 Int)(flted168 Int))(and 
(= color 1)
(= flted166 (+ 1 ha))
(= flted167 1)
(= flted168 (+ (+ (+ 2 nb) na) nc))
(tobool  
(rb res flted168 flted167 flted166)
 )
))
))

(check-sat)