(declare-datatypes (T) ((Lst nil (cons (hd T) (tl Lst)))))
(declare-var l1 (Lst Int))
(declare-var l2 (Lst Int))

(declare-rel rev ((Lst Int) (Lst Int)))
(declare-rel app ((Lst Int) (Lst Int) (Lst Int)))

(rule (forall ((l (Lst Int))) (=> (= l nil) (rev l l))))

;(query (=> (and (= l1 nil) (rev l1 l2)) (rev nil l2)) :print-certificate true)

(query (and (= l2 nil) (rev l1 l2) (not (= l1 nil))) :print-certificate true)
;(query (or (not (and (= l2 nil) (rev l1 l2))) (= l1 nil)) :print-certificate true)
