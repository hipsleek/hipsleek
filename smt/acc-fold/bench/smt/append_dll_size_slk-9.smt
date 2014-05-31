(set-logic QF_S)

(declare-sort node2 0)
(declare-fun val () (Field node2 int))
(declare-fun prev () (Field node2 node2))
(declare-fun next () (Field node2 node2))

(declare-fun dll ((?in node2) (?p node2) (?n int))
Space (tospace
(or
(= ?in nil)
(= ?n 0)
(exists ((?p_23 node2)(?self_24 node2)(?flted_12_22 int)) (tobool (ssep (pto ?in (sref (ref val ?Anon_13) (ref prev ?p_23) (ref next ?q) )) (dll ?q ?self_24 ?flted_12_22)))
)))













(declare-fun n () int)
(declare-fun p () TVar[653])
(declare-fun self_1177 () node2)
(declare-fun q () node2)
(declare-fun m () int)
(declare-fun y () node2)
(declare-fun x () node2)
(declare-fun v_bool_20_1015prm () boolean)
(declare-fun next_21_1070 () node2)
(declare-fun q_1060 () node2)
(declare-fun v_bool_22_1010prm () boolean)
(declare-fun prev_23_1181 () TVar[653])
(declare-fun p_1176 () TVar[653])
(declare-fun Anon_1059 () int)
(declare-fun yprm () node2)
(declare-fun Anon_1179 () int)
(declare-fun q_1180 () node2)
(declare-fun xprm () node2)
(declare-fun flted_12_1178 () int)
(declare-fun p_1056 () node2)
(declare-fun self_1057 () node2)
(declare-fun flted_12_1058 () int)


(assert 
(and 
(= flted_12_1178+1 n)
(= p_1176 p)
(= self_1177 y')
(= flted_12_1058+1 m)
(= p_1056 q)
(= self_1057 x')
lt(= y' y)
(= x' x)
(= q_1060 nil)
bvar(= q_1060 nil)
bvar(= next_21_1070 q_1060)
(distinct y' nil)
bvar(distinct y' nil)
bvar(= prev_23_1181 p_1176)
(tobool (ssep 
(dll q_1060 self_1057 flted_12_1058)
(dll q_1180 self_1177 flted_12_1178)
(pto xprm (sref (ref val Anon_1059) (ref prev p_1056) (ref next y') ))
(pto yprm (sref (ref val Anon_1179) (ref prev x') (ref next q_1180) ))
emp
) )
)
)

(assert (not 
(exists ((flted_18_51 int)(q_54 node2)(Anon_1199 TVar[1589])(q_1200 TVar[1590])(Anon_1211 TVar[1591])(q_1212 TVar[1592])) (tobool (ssep (dll x q_54 flted_18_51) (dll q_1060 self_1057 flted_12_1058)))

))

(check-sat)