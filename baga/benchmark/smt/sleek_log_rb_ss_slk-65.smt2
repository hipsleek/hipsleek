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





































































































































































































































































































































































(declare-fun v21 () Int)
(declare-fun l13 () node)
(declare-fun r13 () node)
(declare-fun tmp_8224 () node)
(declare-fun Anon8 () Int)
(declare-fun flted123 () Int)
(declare-fun flted122 () Int)
(declare-fun cprm () node)
(declare-fun c () node)
(declare-fun bprm () node)
(declare-fun b () node)
(declare-fun aprm () node)
(declare-fun a () node)
(declare-fun flted121 () Int)
(declare-fun bhl13 () Int)
(declare-fun nl13 () Int)
(declare-fun flted119 () Int)
(declare-fun flted118 () Int)
(declare-fun nr13 () Int)
(declare-fun bhr13 () Int)
(declare-fun Anon9 () Int)
(declare-fun n () Int)
(declare-fun bh () Int)
(declare-fun cl () Int)
(declare-fun n3 () Int)
(declare-fun bh3 () Int)
(declare-fun cl3 () Int)
(declare-fun flted120 () Int)
(declare-fun flted132_8221 () Int)
(declare-fun flted131_8220 () Int)
(declare-fun flted130_8219 () Int)
(declare-fun na4 () Int)
(declare-fun ha () Int)
(declare-fun nb4 () Int)
(declare-fun nc4 () Int)
(declare-fun v51_8222 () Int)
(declare-fun v52_8223 () Int)
(declare-fun v50prm () node)
(declare-fun res () node)
(declare-fun nc () Int)
(declare-fun nb () Int)
(declare-fun h () Int)
(declare-fun na () Int)


(assert 
(exists ((flted130 Int)(flted131 Int)(flted132 Int)(v51prm Int)(v52prm Int)(tmpprm node))(and 
;lexvar(= cl3 0)
(<= Anon8 1)
(<= 0 Anon8)
(<= 1 bhl13)
(<= 0 nl13)
(= bh3 bhl13)
(= cl3 Anon8)
(= n3 nl13)
(distinct c nil)
(distinct b nil)
(= flted123 (+ 1 h))
(= flted122 0)
(= flted121 (+ 1 h))
(= flted120 0)
(= cprm c)
(= bprm b)
(= aprm a)
(= flted121 (+ bhl13 1))
(= bhl13 bhr13)
(= nb (+ (+ nr13 1) nl13))
(= flted119 0)
(= flted118 0)
(= n nr13)
(= cl Anon9)
(= bh bhr13)
(<= 0 nr13)
(<= 1 bhr13)
(<= 0 Anon9)
(<= Anon9 1)
(= cl 0)
(= na4 na)
(= ha h)
(= nb4 n3)
(= nc4 n)
(<= 0 n)
(<= 1 bh)
(<= 0 cl)
(<= cl 1)
(<= 0 n3)
(<= 1 bh3)
(<= 0 cl3)
(<= cl3 1)
(<= 0 na)
(<= 1 h)
(<= 0 flted120)
(<= flted120 1)
(= flted132 (+ (+ (+ 2 nb4) na4) nc4))
(= flted131 0)
(= flted130 (+ 1 ha))
(<= 0 na4)
(<= 1 ha)
(<= 0 nb4)
(<= 0 nc4)
(= v51prm 0)
(= v52prm 0)
(= res v50prm)
(tobool (ssep 
(pto bprm (sref (ref val v21) (ref color flted118) (ref left l13) (ref right r13) ))
(rb c nc flted122 flted123)
(rb tmpprm flted132 flted131 flted130)
(pto v50prm (sref (ref val v51prm) (ref color v52prm) (ref left tmpprm) (ref right cprm) ))
) )
))
)

(assert (not 
(exists ((flted133 Int)(flted134 Int)(flted135 Int))(and 
(= flted133 (+ 2 h))
(= flted134 0)
(= flted135 (+ (+ (+ 2 nb) na) nc))
(<= 0 nc)
(<= 0 nb)
(<= 1 h)
(<= 0 na)
(tobool  
(rb res flted135 flted134 flted133)
 )
))
))

(check-sat)