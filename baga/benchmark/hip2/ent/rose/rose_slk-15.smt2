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



























(declare-fun c2_317 () tree)
(declare-fun n_319 () node)
(declare-fun l () node)
(declare-fun pprm () tree)
(declare-fun p1 () tree)
(declare-fun lprm () node)
(declare-fun parent1_316 () tree)
(declare-fun parent_315 () tree)
(declare-fun p3 () tree)
(declare-fun Anon3 () Int)
(declare-fun s_318 () Int)
(declare-fun s1_320 () Int)


(assert 
(exists ((parent tree)(parent1 tree)(c2 tree)(s Int)(n node)(s1 Int))(and 
;lexvar(= lprm l)
(= pprm p1)
(= p3 p1)
(distinct lprm nil)
(not )(= parent1 p3)
(= parent p3)
(= Anon3 (+ s1 s))
(tobool (ssep 
(treep c2 s)
(pto lprm (sref (ref child c2) (ref next n) (ref parent parent) ))
(sll n parent1 s1)
) )
))
)

(assert (not 
(and 
(tobool  
(pto lprm (sref (ref child childprm) (ref next nextprm) (ref parent parentprm) ))
 )
)
))

(check-sat)