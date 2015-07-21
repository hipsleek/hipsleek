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
(declare-fun n1 () node)
(declare-fun Anon3 () tree)
(declare-fun parent2 () tree)
(declare-fun p3 () tree)
(declare-fun p1 () tree)
(declare-fun lprm () node)
(declare-fun l () node)
(declare-fun pprm () tree)
(declare-fun parent3 () tree)
(declare-fun Anon4 () tree)
(declare-fun s2 () tree)
(declare-fun Anon () tree)
(declare-fun s3 () tree)


(assert 
(exists ((v9prm boolean)(v11prm boolean))(and 
;lexvar(= Anon3 (+ s2 s3))
(= parent3 p3)
(= parent2 p3)
(not )(distinct lprm nil)
(= p3 p1)
(= pprm p1)
(= lprm l)
(= pprm parent3)
(= Anon4 s2)
(= Anon s3)
(= res v13prm)
(tobool  
(pto lprm (sref (ref child c3) (ref next n1) (ref parent parent3) ))
 )
))
)

(assert (not 

))

(check-sat)