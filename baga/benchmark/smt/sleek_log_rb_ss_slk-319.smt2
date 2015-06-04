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





































































































































































































































































































































































(declare-fun Anon33 () Int)
(declare-fun r45 () node)
(declare-fun v100 () Int)
(declare-fun l47 () node)
(declare-fun v139prm () node)
(declare-fun r47 () node)
(declare-fun flted350 () Int)
(declare-fun flted348 () Int)
(declare-fun nr47 () Int)
(declare-fun bhr47 () Int)
(declare-fun bh39 () Int)
(declare-fun cl () Int)
(declare-fun Anon38 () Int)
(declare-fun n17 () Int)
(declare-fun left1 () node)
(declare-fun bh38 () Int)
(declare-fun v98 () node)
(declare-fun flted344 () Int)
(declare-fun bh34 () Int)
(declare-fun Anon34 () Int)
(declare-fun Anon32 () Int)
(declare-fun n16 () Int)
(declare-fun tmpprm () node)
(declare-fun l45 () node)
(declare-fun x () node)
(declare-fun v90 () Int)
(declare-fun tmp1prm () node)
(declare-fun xprm () node)
(declare-fun bh () Int)
(declare-fun bhl45 () Int)
(declare-fun bhr45 () Int)
(declare-fun n () Int)
(declare-fun nl45 () Int)
(declare-fun nr45 () Int)
(declare-fun Anon29 () Int)
(declare-fun flted340 () Int)
(declare-fun v125prm () Int)
(declare-fun v94 () Int)
(declare-fun nl47 () Int)
(declare-fun bhl47 () Int)
(declare-fun flted349 () Int)
(declare-fun n18 () Int)
(declare-fun bh40 () Int)
(declare-fun cl24 () Int)


(assert 
(and 
;lexvar(= v139prm r47)
(= flted350 1)
(= flted349 0)
(= flted348 0)
(= n17 (+ (+ nr47 1) nl47))
(= bhl47 bh39)
(= bhr47 bh39)
(<= cl 1)
(<= 0 cl)
(<= 1 bh39)
(<= 0 n17)
(= cl 1)
(<= Anon38 1)
(<= 0 Anon38)
(<= 1 bh38)
(<= 0 flted344)
(= bh39 bh38)
(= cl Anon38)
(= n17 flted344)
(= left1 l45)
(<= Anon34 1)
(<= 0 Anon34)
(<= 1 bh34)
(<= 0 n16)
(<= bh38 bh34)
(<= bh34 bh38)
(distinct v98 nil)
(= flted344 (+ 1 n16))
(<= Anon32 1)
(<= 0 Anon32)
(<= 1 bhl45)
(<= 0 nl45)
(= bh34 bhl45)
(= Anon34 Anon32)
(= n16 nl45)
(= tmpprm l45)
(= xprm x)
(= v125prm v90)
(= tmp1prm nil)
(distinct xprm nil)
(= bh (+ bhl45 1))
(= bhl45 bhr45)
(= n (+ (+ nr45 1) nl45))
(= Anon29 0)
(= flted340 0)
(<= v125prm v94)
(= n18 nl47)
(= cl24 flted349)
(= bh40 bhl47)
(<= 0 nl47)
(<= 1 bhl47)
(<= 0 flted349)
(<= flted349 1)
(= cl24 0)
(<= 0 n18)
(<= 1 bh40)
(<= 0 cl24)
(<= cl24 1)
(tobool (ssep 
(rb r45 nr45 Anon33 bhr45)
(pto xprm (sref (ref val v94) (ref color flted340) (ref left v98) (ref right r45) ))
(pto v98 (sref (ref val v100) (ref color flted350) (ref left l47) (ref right r47) ))
(rb r47 nr47 flted348 bhr47)
(rb l47 n18 cl24 bh40)
) )
)
)

(assert (not 
(and 
(tobool  
(rb v139prm n19 cl25 bh41)
 )
)
))

(check-sat)