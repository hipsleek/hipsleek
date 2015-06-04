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





































































































































































































































































































































































(declare-fun v153prm () node)
(declare-fun v154_34171 () Int)
(declare-fun x () node)
(declare-fun v125prm () Int)
(declare-fun v90 () Int)
(declare-fun xprm () node)
(declare-fun tmp1_34173 () node)
(declare-fun tmp1_34172 () node)
(declare-fun res () node)
(declare-fun Anon29 () Int)
(declare-fun bh () Int)
(declare-fun n () Int)


(assert 
(exists ((v154prm Int)(tmp1prm node))(and 
;lexvar(= res v153prm)
(= v154prm 1)
(= xprm x)
(= v125prm v90)
(= tmp1prm nil)
(= xprm nil)
(tobool (ssep 
(rb x n Anon29 bh)
(pto v153prm (sref (ref val v125prm) (ref color v154prm) (ref left tmp1prm) (ref right tmp1prm) ))
) )
))
)

(assert (not 
(exists ((flted361 Int)(Anon44 Int)(bh50 Int))(and 
(<= bh50 bh)
(<= bh bh50)
(distinct res nil)
(= flted361 (+ 1 n))
(<= Anon29 1)
(<= 0 Anon29)
(<= 1 bh)
(<= 0 n)
(tobool  
(rb res flted361 Anon44 bh50)
 )
))
))

(check-sat)