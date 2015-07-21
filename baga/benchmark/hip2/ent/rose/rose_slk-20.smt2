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



























(declare-fun c3 () tree)
(declare-fun Anon4 () Int)
(declare-fun v8prm () node)
(declare-fun n1 () node)
(declare-fun l () node)
(declare-fun pprm () tree)
(declare-fun p1 () tree)
(declare-fun lprm () node)
(declare-fun parent2 () tree)
(declare-fun parent3 () tree)
(declare-fun p3 () tree)
(declare-fun Anon3 () Int)
(declare-fun s3 () Int)
(declare-fun s2 () Int)


(assert 
(and 
;lexvar(= Anon4 s2)
(= v8prm n1)
(= pprm parent3)
(= lprm l)
(= pprm p1)
(= p3 p1)
(distinct lprm nil)
(not )(= parent2 p3)
(= parent3 p3)
(= Anon3 (+ s2 s3))
(tobool (ssep 
(treep c3 s3)
(pto lprm (sref (ref child c3) (ref next n1) (ref parent parent3) ))
) )
)
)

(assert (not 
;lexvar
))

(check-sat)