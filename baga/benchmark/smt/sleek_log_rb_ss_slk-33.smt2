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





































































































































































































































































































































































(declare-fun v17_5223 () Int)
(declare-fun l9_5224 () node)
(declare-fun Anon2_5226 () Int)
(declare-fun r9_5228 () node)
(declare-fun Anon3_5230 () Int)
(declare-fun x () node)
(declare-fun xprm () node)
(declare-fun bh () Int)
(declare-fun bhl9_5227 () Int)
(declare-fun bhr9_5231 () Int)
(declare-fun n () Int)
(declare-fun nl9_5225 () Int)
(declare-fun nr9_5229 () Int)
(declare-fun cl () Int)
(declare-fun flted107_5222 () Int)


(assert 
(exists ((flted107 Int)(v17 Int)(l9 node)(nl9 Int)(Anon2 Int)(bhl9 Int)(r9 node)(nr9 Int)(Anon3 Int)(bhr9 Int))(and 
;lexvar(= xprm x)
(distinct xprm nil)
(= bh (+ bhl9 1))
(= bhl9 bhr9)
(= n (+ (+ nr9 1) nl9))
(= cl 0)
(= flted107 0)
(tobool (ssep 
(pto xprm (sref (ref val v17) (ref color flted107) (ref left l9) (ref right r9) ))
(rb l9 nl9 Anon2 bhl9)
(rb r9 nr9 Anon3 bhr9)
) )
))
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val1prm) (ref color color2prm) (ref left left1prm) (ref right right1prm) ))
 )
)
))

(check-sat)