(declare-fun rev ((List Int)) (List Int))
(assert (forall ((l (List Int))) (=> (= l nil) (= l (rev l)))))
(assert (forall ((l1 (List Int))) (exists ((l2 (List Int))) (=> (and
(= l1 nil) (= l1 (rev l2))) (= nil l2)))))
(assert (forall ((l1 (List Int)) (l2 (List Int))) (=> (and
(= l2 (rev l1) (= l1 (rev l2)))) (= l1 l2))))
(check-sat)
