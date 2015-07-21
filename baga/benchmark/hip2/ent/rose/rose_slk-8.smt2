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



























(declare-fun Anon2 () Int)
(declare-fun Anon3 () Int)
(declare-fun v2prm () node)
(declare-fun flted1 () Int)
(declare-fun Anon () Int)
(declare-fun self1 () tree)
(declare-fun tprm () tree)
(declare-fun t () tree)
(declare-fun c1 () node)


(assert 
(and 
;lexvar(= Anon3 flted1)
(= v2prm c1)
(= (+ flted1 1) Anon)
(= self1 tprm)
(= tprm t)
(distinct c1 nil)
(not )(tobool  
(pto tprm (sref (ref val Anon2) (ref children c1) ))
 )
)
)

(assert (not 
;lexvar
))

(check-sat)