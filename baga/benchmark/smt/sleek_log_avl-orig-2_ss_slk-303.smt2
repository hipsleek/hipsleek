(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun ele () (Field node Int))
(declare-fun height () (Field node Int))
(declare-fun left () (Field node node))
(declare-fun right () (Field node node))

(define-fun avl ((?in node) (?m Int) (?n Int) (?bal Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?m 0)
(= ?n 0)
(= ?bal 1)

)(exists ((?n_80 Int))(and 
(= ?m (+ (+ ?m2 1) ?m1))
(<= (+ 0 ?n2) (+ ?n1 1))
(<= ?n1 (+ 1 ?n2))
(= (+ ?bal ?n2) (+ 1 ?n1))
(= ?n_80 ?n)
(tobool (ssep 
(pto ?in (sref (ref ele ?Anon_14) (ref height ?n_80) (ref left ?p) (ref right ?q) ))
(avl ?p ?m1 ?n1 ?Anon_15)
(avl ?q ?m2 ?n2 ?Anon_16)
) )
)))))






































































































































































































































































































































(declare-fun v77prm () node)
(declare-fun v78_37814 () Int)
(declare-fun xprm () Int)
(declare-fun x () Int)
(declare-fun tprm () node)
(declare-fun tmp_37816 () node)
(declare-fun tmp_37815 () node)
(declare-fun res () node)
(declare-fun t6 () node)
(declare-fun b () Int)
(declare-fun tn () Int)
(declare-fun tm () Int)


(assert 
(exists ((v78prm Int)(tmpprm node))(and 
;lexvar(= res v77prm)
(= v78prm 1)
(= tprm t6)
(= xprm x)
(= tmpprm nil)
(= tprm nil)
(tobool (ssep 
(avl t6 tm tn b)
(pto v77prm (sref (ref ele xprm) (ref height v78prm) (ref left tmpprm) (ref right tmpprm) ))
) )
))
)

(assert (not 
(exists ((flted29 Int)(flted30 Int)(flted31 Int))(and 
(= t6 nil)
(= tm 0)
(= tn 0)
(= flted29 1)
(= flted30 1)
(= flted31 1)
(<= b 2)
(<= 0 b)
(<= 0 tn)
(<= 0 tm)
(tobool  
(avl res flted31 flted30 flted29)
 )
))
))

(check-sat)