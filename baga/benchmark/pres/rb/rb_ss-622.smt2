(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun flted_121_7830 () Int)
(declare-fun nd () Int)
(declare-fun na () Int)
(declare-fun nc () Int)
(declare-fun nb () Int)
(declare-fun flted_121_7828 () Int)
(declare-fun h () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (and (and (and (and (and (and (and (and (and (exists ((flted_153_326 Int)) (and (<= 0 flted_153_326) (<= flted_153_326 1))) (exists ((flted_153_325 Int)) (and (<= 0 flted_153_325) (<= flted_153_325 1)))) (exists ((flted_153_324 Int)) (and (<= 0 flted_153_324) (<= flted_153_324 1)))) (exists ((flted_153_323 Int)) (and (<= 0 flted_153_323) (<= flted_153_323 1)))) (exists ((h_329 Int)) (<= 1 h_329))) (exists ((h_328 Int)) (<= 1 h_328))) (exists ((h_327 Int)) (<= 1 h_327))) (<= 0 na)) (<= 1 h)) (<= 0 nb)) (<= 0 nc)) (<= 0 nd)) (and (and (and (and (and (and (and (and (and (and (and (exists ((flted_154_322 Int)) (and (<= 0 flted_154_322) (<= flted_154_322 1))) (exists ((flted_154_321 Int)) (and (<= 0 flted_154_321) (<= flted_154_321 1)))) (exists ((flted_154_320 Int)) (and (<= 0 flted_154_320) (<= flted_154_320 1)))) (exists ((flted_154_319 Int)) (and (<= 0 flted_154_319) (<= flted_154_319 1)))) (exists ((h_332 Int)) (<= 1 h_332))) (exists ((h_331 Int)) (<= 1 h_331))) (exists ((h_330 Int)) (<= 1 h_330))) (<= 0 na)) (<= 1 h)) (<= 0 nb)) (<= 0 nc)) (<= 0 nd))))
(assert (= flted_121_7830 (+ (+ (+ (+ nd na) 3) nc) nb)))
(assert (= flted_121_7828 (+ h 1)))
;Negation of Consequence
(assert (not false))
(check-sat)