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





































































































































































































































































































































































(declare-fun v27 () Int)
(declare-fun l19 () node)
(declare-fun r19 () node)
(declare-fun tmp_10649 () node)
(declare-fun v59prm () node)
(declare-fun v62_10648 () Int)
(declare-fun v61_10647 () Int)
(declare-fun v60_10646 () Int)
(declare-fun color4 () Int)
(declare-fun flted169 () Int)
(declare-fun flted170 () Int)
(declare-fun flted171 () Int)
(declare-fun flted172 () Int)
(declare-fun nl19 () Int)
(declare-fun nr19 () Int)
(declare-fun bhl19 () Int)
(declare-fun bhr19 () Int)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun colorprm () Int)
(declare-fun flted173 () Int)
(declare-fun ha9 () Int)
(declare-fun ha10 () Int)
(declare-fun v58_10645 () Int)
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
(= color4 flted169)
(= flted169 1)
(= flted170 0)
(= flted171 0)
(= flted172 1)
(= na (+ (+ nr19 1) nl19))
(= bhl19 ha)
(= bhr19 ha)
(= aprm a)
(= bprm b)
(= cprm c)
(= colorprm color)
(= flted173 0)
(= color 1)
(= ha9 ha)
(= ha10 ha)
(= v58prm 0)
(tobool (ssep 
(rb l19 nl19 flted170 bhl19)
(rb r19 nr19 flted171 bhr19)
(rb b nb Anon11 ha9)
(rb c nc flted173 ha10)
(pto aprm (sref (ref val v27) (ref color v58prm) (ref left l19) (ref right r19) ))
(pto tmpprm (sref (ref val v60prm) (ref color v61prm) (ref left bprm) (ref right cprm) ))
(pto v59prm (sref (ref val v62prm) (ref color colorprm) (ref left aprm) (ref right tmpprm) ))
) )
))
)

(assert (not 
(exists ((flted163 Int)(flted164 Int)(flted165 Int))(and 
(= color 0)
(= flted163 (+ 2 ha))
(= flted164 0)
(= flted165 (+ (+ (+ 2 nb) na) nc))
(tobool  
(rb res flted165 flted164 flted163)
 )
))
))

(check-sat)