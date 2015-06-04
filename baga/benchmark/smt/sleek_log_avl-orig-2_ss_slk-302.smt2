(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


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
(declare-fun v78_37726 () Int)
(declare-fun xprm () Int)
(declare-fun x () Int)
(declare-fun tprm () node)
(declare-fun tmp_37728 () node)
(declare-fun tmp_37727 () node)
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
(exists ((flted28 Int)(resn16 Int)(resb4 Int))(and 
(< 0 tn)
(< 0 tm)
(distinct t6 nil)
(= flted28 (+ 1 tm))
(<= b 2)
(<= 0 b)
(<= 0 tn)
(<= 0 tm)
(tobool  
(avl res flted28 resn16 resb4)
 )
))
))

(check-sat)