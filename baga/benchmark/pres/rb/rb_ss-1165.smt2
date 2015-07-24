(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun bhl_10164 () Int)
(declare-fun nl_10162 () Int)
(declare-fun nr_10166 () Int)
(declare-fun Anon_19 () Int)
(declare-fun na () Int)
(declare-fun ha () Int)
(declare-fun nb () Int)
(declare-fun Anon_20 () Int)
(declare-fun nc () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= (+ 1 bhl_10164) (+ ha 1)))
(assert (= (+ (+ nl_10162 nr_10166) 1) (+ (+ (+ nc nb) 2) na)))
(assert (or (and (and (and (and (and (and (and (and (and (exists ((flted_136_364 Int)) (and (<= 0 flted_136_364) (<= flted_136_364 1))) (exists ((flted_136_363 Int)) (and (<= 0 flted_136_363) (<= flted_136_363 1)))) (exists ((ha_366 Int)) (<= 1 ha_366))) (exists ((ha_365 Int)) (<= 1 ha_365))) (<= 0 na)) (<= 1 ha)) (<= 0 nb)) (<= 0 Anon_19)) (<= Anon_19 1)) (<= 0 nc)) (and (and (and (and (and (and (and (and (and (exists ((flted_137_362 Int)) (and (<= 0 flted_137_362) (<= flted_137_362 1))) (exists ((flted_137_361 Int)) (and (<= 0 flted_137_361) (<= flted_137_361 1)))) (exists ((ha_368 Int)) (<= 1 ha_368))) (exists ((ha_367 Int)) (<= 1 ha_367))) (<= 0 na)) (<= 1 ha)) (<= 0 nb)) (<= 0 Anon_20)) (<= Anon_20 1)) (<= 0 nc))))
;Negation of Consequence
(assert (not false))
(check-sat)