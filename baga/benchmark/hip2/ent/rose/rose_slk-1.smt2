(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/hip/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node 0)
(declare-fun child () (Field node tree))
(declare-fun next () (Field node node))
(declare-fun parent () (Field node tree))

(declare-sort tree 0)
(declare-fun val () (Field tree Int))
(declare-fun children () (Field tree node))

(define-fun treep ((?in tree) (?n Int))
Space (tospace
(exists ((?self_35 tree)(?flted_13_34 Int))(and 
(= (+ ?flted_13_34 1) ?n)
(= ?self_35 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_15) (ref children ?c) ))
(sll ?c ?self_35 ?flted_13_34)
) )
))))

(define-fun sll ((?in node) (?parent tree) (?s Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?s 0)

)(exists ((?parent_31 tree)(?parent_32 tree))(and 
(= ?s (+ ?s2 ?s1))
(= ?parent_31 ?parent)
(= ?parent_32 ?parent)
(tobool (ssep 
(pto ?in (sref (ref child ?c) (ref next ?n) (ref parent ?parent_31) ))
(treep ?c ?s1)
(sll ?n ?parent_32 ?s2)
) )
)))))



























(declare-fun Anon1_65 () Int)
(declare-fun c_66 () node)
(declare-fun flted_64 () Int)
(declare-fun Anon () Int)
(declare-fun self_63 () tree)
(declare-fun tprm () tree)
(declare-fun t () tree)


(assert 
(exists ((self tree)(flted Int)(Anon1 Int)(c node))(and 
;lexvar(= (+ flted 1) Anon)
(= self tprm)
(= tprm t)
(tobool (ssep 
(pto tprm (sref (ref val Anon1) (ref children c) ))
(sll c self flted)
) )
))
)

(assert (not 
(and 
(tobool  
(pto tprm (sref (ref val valprm) (ref children childrenprm) ))
 )
)
))

(check-sat)