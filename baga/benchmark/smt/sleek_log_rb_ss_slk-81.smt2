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





































































































































































































































































































































































(declare-fun bhr20 () Int)
(declare-fun nr20 () Int)
(declare-fun bhl20 () Int)
(declare-fun nl20 () Int)
(declare-fun r20 () node)
(declare-fun l20 () node)
(declare-fun v29 () Int)
(declare-fun v28 () Int)
(declare-fun v30 () Int)
(declare-fun dprm () node)
(declare-fun d () node)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun flted185 () Int)
(declare-fun flted184 () Int)
(declare-fun flted183 () Int)
(declare-fun flted182 () Int)
(declare-fun tmp_12260 () node)
(declare-fun flted196_12259 () Int)
(declare-fun flted195_12258 () Int)
(declare-fun flted194_12257 () Int)
(declare-fun colorprm () Int)
(declare-fun Anon10 () Int)
(declare-fun na7 () Int)
(declare-fun ha () Int)
(declare-fun nb7 () Int)
(declare-fun Anon11 () Int)
(declare-fun nc7 () Int)
(declare-fun v65prm () node)
(declare-fun res () node)
(declare-fun color () Int)
(declare-fun na () Int)
(declare-fun h () Int)
(declare-fun nb () Int)
(declare-fun nc () Int)
(declare-fun nd () Int)


(assert 
(exists ((flted194 Int)(flted195 Int)(flted196 Int)(tmpprm Int))(and 
;lexvar(= na7 (+ (+ nr20 1) nl20))
(= bhl20 ha)
(= bhr20 ha)
(= bhr20 bhl20)
(= bhr20 h)
(= nr20 nb)
(= bhl20 h)
(= nl20 na)
(= r20 bprm)
(= l20 aprm)
(= v29 v30)
(= v28 1)
(= v30 0)
(= color 0)
(= flted185 0)
(= flted184 0)
(= flted183 0)
(= flted182 0)
(= colorprm color)
(= dprm d)
(= cprm c)
(= bprm b)
(= aprm a)
(= nb7 nc)
(= Anon10 flted184)
(= nc7 nd)
(<= 0 nd)
(<= 0 flted185)
(<= flted185 1)
(<= 0 nc)
(<= 0 flted184)
(<= flted184 1)
(<= 0 nb)
(<= 0 flted183)
(<= flted183 1)
(<= 0 na)
(<= 1 h)
(<= 0 flted182)
(<= flted182 1)
(distinct tmpprm nil)
(= flted196 (+ (+ (+ 2 nb7) na7) nc7))
(= flted195 0)
(= flted194 (+ 2 ha))
(= colorprm 0)
(= res v65prm)
(tobool  
(rb v65prm flted196 flted195 flted194)
 )
))
)

(assert (not 
(exists ((flted197 Int)(flted198 Int)(flted199 Int))(and 
(= color 0)
(= flted197 (+ 2 h))
(= flted198 0)
(= flted199 (+ (+ (+ (+ 3 nc) na) nb) nd))
(tobool  
(rb res flted199 flted198 flted197)
 )
))
))

(check-sat)