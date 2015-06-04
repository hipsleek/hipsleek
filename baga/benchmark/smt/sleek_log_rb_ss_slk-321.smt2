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
(declare-fun r47 () node)
(declare-fun bh40 () Int)
(declare-fun cl24 () Int)
(declare-fun n18 () Int)
(declare-fun v94 () Int)
(declare-fun flted340 () Int)
(declare-fun Anon29 () Int)
(declare-fun n () Int)
(declare-fun nr45 () Int)
(declare-fun bhr45 () Int)
(declare-fun bh () Int)
(declare-fun tmp1prm () node)
(declare-fun v125prm () Int)
(declare-fun v90 () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun tmpprm () node)
(declare-fun nl45 () Int)
(declare-fun bhl45 () Int)
(declare-fun Anon32 () Int)
(declare-fun v98 () node)
(declare-fun n16 () Int)
(declare-fun bh34 () Int)
(declare-fun Anon34 () Int)
(declare-fun left1 () node)
(declare-fun l45 () node)
(declare-fun flted344 () Int)
(declare-fun bh38 () Int)
(declare-fun Anon38 () Int)
(declare-fun cl () Int)
(declare-fun bhl47 () Int)
(declare-fun bh39 () Int)
(declare-fun n17 () Int)
(declare-fun nl47 () Int)
(declare-fun flted349 () Int)
(declare-fun flted350 () Int)
(declare-fun nr47 () Int)
(declare-fun bhr47 () Int)
(declare-fun flted348 () Int)
(declare-fun n19 () Int)
(declare-fun bh41 () Int)
(declare-fun cl25 () Int)


(assert 
(and 
;lexvar(<= cl24 1)
(<= 0 cl24)
(<= 1 bh40)
(<= 0 n18)
(= cl24 0)
(<= flted349 1)
(<= 0 flted349)
(<= 1 bhl47)
(<= 0 nl47)
(= bh40 bhl47)
(= cl24 flted349)
(= n18 nl47)
(<= v125prm v94)
(= flted340 0)
(= Anon29 0)
(= n (+ (+ nr45 1) nl45))
(= bhl45 bhr45)
(= bh (+ bhl45 1))
(distinct xprm nil)
(= tmp1prm nil)
(= v125prm v90)
(= xprm x)
(= tmpprm l45)
(= n16 nl45)
(= Anon34 Anon32)
(= bh34 bhl45)
(<= 0 nl45)
(<= 1 bhl45)
(<= 0 Anon32)
(<= Anon32 1)
(= flted344 (+ 1 n16))
(distinct v98 nil)
(<= bh34 bh38)
(<= bh38 bh34)
(<= 0 n16)
(<= 1 bh34)
(<= 0 Anon34)
(<= Anon34 1)
(= left1 l45)
(= n17 flted344)
(= cl Anon38)
(= bh39 bh38)
(<= 0 flted344)
(<= 1 bh38)
(<= 0 Anon38)
(<= Anon38 1)
(= cl 1)
(<= 0 n17)
(<= 1 bh39)
(<= 0 cl)
(<= cl 1)
(= bhr47 bh39)
(= bhl47 bh39)
(= n17 (+ (+ nr47 1) nl47))
(= flted348 0)
(= flted349 0)
(= flted350 1)
(= n19 nr47)
(= cl25 flted348)
(= bh41 bhr47)
(<= 0 nr47)
(<= 1 bhr47)
(<= 0 flted348)
(<= flted348 1)
(= cl25 0)
(<= 0 n19)
(<= 1 bh41)
(<= 0 cl25)
(<= cl25 1)
(tobool (ssep 
(rb r45 nr45 Anon33 bhr45)
(pto xprm (sref (ref val v94) (ref color flted340) (ref left v98) (ref right r45) ))
(pto v98 (sref (ref val v100) (ref color flted350) (ref left l47) (ref right r47) ))
(rb l47 n18 cl24 bh40)
(rb r47 n19 cl25 bh41)
) )
)
)

(assert (not 
(and 
(tobool  
(htrue )
 )
)
))

(check-sat)