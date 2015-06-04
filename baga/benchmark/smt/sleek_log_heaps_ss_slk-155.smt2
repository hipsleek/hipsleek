(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun nleft () (Field node Int))
(declare-fun nright () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun pq ((?in node) (?n Int) (?mx Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)
(= ?mx 0)

)(exists ((?m1_28 Int)(?m2_29 Int)(?m3_27 Int))(and 
(= ?n (+ (+ ?m2 1) ?m1))
(<= 0 ?d)
(<= ?mx1 ?d)
(<= ?mx2 ?d)
(<= ?d ?mx)
(= (+ ?m3_27 ?m2) ?m1)
(<= 0 ?m3_27)
(<= ?m3_27 1)
(= ?m1_28 ?m1)
(= ?m2_29 ?m2)
(tobool (ssep 
(pto ?in (sref (ref val ?d) (ref nleft ?m1) (ref nright ?m2) (ref left ?l) (ref right ?r) ))
(pq ?l ?m1_28 ?mx1)
(pq ?r ?m2_29 ?mx2)
) )
)))))
































































































































































(declare-fun v66prm () node)
(declare-fun v68_10727 () Int)
(declare-fun v67_10726 () Int)
(declare-fun t () node)
(declare-fun v13prm () Int)
(declare-fun tprm () node)
(declare-fun tmp1_10729 () node)
(declare-fun tmp1_10728 () node)
(declare-fun res () node)
(declare-fun v12 () Int)
(declare-fun mx () Int)
(declare-fun n () Int)


(assert 
(exists ((v67prm Int)(v68prm Int)(tmp1prm node))(and 
;lexvar(= res v66prm)
(= v68prm 0)
(= v67prm 0)
(= tprm t)
(= v13prm v12)
(<= 0 v12)
(= tmp1prm nil)
(= tprm nil)
(tobool (ssep 
(pq t n mx)
(pto v66prm (sref (ref val v13prm) (ref nleft v67prm) (ref nright v68prm) (ref left tmp1prm) (ref right tmp1prm) ))
) )
))
)

(assert (not 
(exists ((n13 Int)(ma8 Int))(and 
(= n13 (+ 1 n))
(<= 0 mx)
(<= 0 n)
(tobool  
(pq res n13 ma8)
 )
))
))

(check-sat)