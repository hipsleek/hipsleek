(set-logic QF_S)
(set-info :source |  Sleek solver
  http://loris-7.ddns.comp.nus.edu.sg/~project/s2/beta/
|)

(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)


(declare-sort node2 0)
(declare-fun val () (Field node2 Int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(define-fun dll ((?in node2) (?p node2) (?n Int))
Space (tospace
(or
(and 
(= ?in nil)
(= ?n 0)

)(exists ((?p_40 node2)(?self_41 node2)(?flted_12_39 Int))(and 
(= (+ ?flted_12_39 1) ?n)
(= ?p_40 ?p)
(= ?self_41 ?in)
(tobool (ssep 
(pto ?in (sref (ref val ?Anon_13) (ref prev ?p_40) (ref next ?q) ))
(dll ?q ?self_41 ?flted_12_39)
) )
)))))








































































































































(declare-fun Anon46 () Int)
(declare-fun Anon47 () node2)
(declare-fun Anon48 () node2)
(declare-fun Anon54 () Int)
(declare-fun q45 () node2)
(declare-fun prev6 () node2)
(declare-fun xprm () node2)
(declare-fun tmp2 () node2)
(declare-fun x () node2)
(declare-fun self38 () node2)
(declare-fun tmp2prm () node2)
(declare-fun p47 () node2)
(declare-fun x2 () node2)
(declare-fun flted51 () Int)
(declare-fun Anon49 () Int)


(assert 
(and 
;lexvar(= prev6 p47)
(= xprm x)
(= tmp2prm tmp2)
(distinct tmp2 nil)
(= x2 x)
(distinct tmp2prm nil)
(= self38 tmp2prm)
(= p47 x2)
(= (+ flted51 1) Anon49)
(tobool (ssep 
(pto x (sref (ref val Anon46) (ref prev Anon47) (ref next Anon48) ))
(dll q45 self38 flted51)
(pto tmp2prm (sref (ref val Anon54) (ref prev xprm) (ref next q45) ))
) )
)
)

(assert (not 
(and 
(tobool  
(pto xprm (sref (ref val val34prm) (ref prev prev34prm) (ref next next34prm) ))
 )
)
))

(check-sat)