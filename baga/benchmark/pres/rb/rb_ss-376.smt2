(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun bhl_6767 () Int)
(declare-fun bhr_6770 () Int)
(declare-fun nl_6766 () Int)
(declare-fun nr_6769 () Int)
(declare-fun Anon_17 () Int)
(declare-fun na () Int)
(declare-fun h () Int)
(declare-fun nb () Int)
(declare-fun Anon_18 () Int)
(declare-fun nc () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (= bhr_6770 (+ h 2)))
(assert (= bhl_6767 bhr_6770))
(assert (= (+ (+ nl_6766 nr_6769) 1) (+ (+ (+ nc nb) 2) na)))
(assert (or (and (and (and (and (and (and (and (and (and (exists ((flted_119_400 Int)) (and (<= 0 flted_119_400) (<= flted_119_400 1))) (exists ((flted_119_399 Int)) (and (<= 0 flted_119_399) (<= flted_119_399 1)))) (exists ((h_402 Int)) (<= 1 h_402))) (exists ((h_401 Int)) (<= 1 h_401))) (<= 0 na)) (<= 1 h)) (<= 0 nb)) (<= 0 Anon_17)) (<= Anon_17 1)) (<= 0 nc)) (and (and (and (and (and (and (and (and (and (exists ((flted_120_398 Int)) (and (<= 0 flted_120_398) (<= flted_120_398 1))) (exists ((flted_120_397 Int)) (and (<= 0 flted_120_397) (<= flted_120_397 1)))) (exists ((h_404 Int)) (<= 1 h_404))) (exists ((h_403 Int)) (<= 1 h_403))) (<= 0 na)) (<= 1 h)) (<= 0 nb)) (<= 0 Anon_18)) (<= Anon_18 1)) (<= 0 nc))))
;Negation of Consequence
(assert (not false))
(check-sat)