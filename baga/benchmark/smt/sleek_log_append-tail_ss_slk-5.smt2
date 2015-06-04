(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)


(declare-sort node 0)
(declare-fun val () (Field node Int))
(declare-fun next () (Field node node))

(define-fun ll_tail2 ((?in node) (?tx node) (?n Int))
Space (tospace
(or
(exists ((?flted_18_27 node))(and 
(= ?flted_18_27 nil)
(= ?tx ?in)
(= ?n 1)
(tobool  
(pto ?in (sref (ref val ?Anon_13) (ref next ?flted_18_27) ))
 )
))(exists ((?tx_29 node)(?flted_19_28 Int))(and 
(= (+ ?flted_19_28 1) ?n)
(distinct ?r nil)
(= ?tx_29 ?tx)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_14) (ref next ?r) ))
(ll_tail2 ?r ?tx_29 ?flted_19_28)
) )
)))))

(define-fun lseg2 ((?in node) (?p node) (?n Int))
Space (tospace
(or
(and 
(= ?in ?p)
(= ?n 0)

)(exists ((?p_32 node)(?flted_15_31 Int))(and 
(= (+ ?flted_15_31 1) ?n)
(= ?p_32 ?p)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_12) (ref next ?r) ))
(lseg2 ?r ?p_32 ?flted_15_31)
) )
)))))








(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun xprm () node)
(declare-fun x () node)
(declare-fun txprm () node)
(declare-fun yprm () node)
(declare-fun y () node)
(declare-fun typrm () node)
(declare-fun tx1_142 () node)
(declare-fun tx () node)
(declare-fun ty1_143 () node)
(declare-fun ty () node)


(assert 
(exists ((tx1 node)(ty1 node))(and 
;lexvar(= xprm x)
(= txprm tx)
(= yprm y)
(= typrm ty)
(= tx1 tx)
(= ty1 ty)
(tobool (ssep 
(ll_tail2 x tx1 n)
(ll_tail2 y ty1 m)
) )
))
)

(assert (not 
(and 
(tobool  
(pto txprm (sref (ref val valprm) (ref next nextprm) ))
 )
)
))

(check-sat)