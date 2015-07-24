(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun flted_139_11527 () Int)
(declare-fun nd () Int)
(declare-fun na () Int)
(declare-fun nc () Int)
(declare-fun nb () Int)
(declare-fun flted_139_11525 () Int)
(declare-fun h () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (and (and (and (and (and (and (and (and (and (exists ((flted_168_280 Int)) (and (<= 0 flted_168_280) (<= flted_168_280 1))) (exists ((flted_168_279 Int)) (and (<= 0 flted_168_279) (<= flted_168_279 1)))) (exists ((flted_168_278 Int)) (and (<= 0 flted_168_278) (<= flted_168_278 1)))) (exists ((flted_168_277 Int)) (and (<= 0 flted_168_277) (<= flted_168_277 1)))) (exists ((h_283 Int)) (<= 1 h_283))) (exists ((h_282 Int)) (<= 1 h_282))) (exists ((h_281 Int)) (<= 1 h_281))) (<= 0 na)) (<= 1 h)) (<= 0 nb)) (<= 0 nc)) (<= 0 nd)) (and (and (and (and (and (and (and (and (and (and (and (exists ((flted_169_276 Int)) (and (<= 0 flted_169_276) (<= flted_169_276 1))) (exists ((flted_169_275 Int)) (and (<= 0 flted_169_275) (<= flted_169_275 1)))) (exists ((flted_169_274 Int)) (and (<= 0 flted_169_274) (<= flted_169_274 1)))) (exists ((flted_169_273 Int)) (and (<= 0 flted_169_273) (<= flted_169_273 1)))) (exists ((h_286 Int)) (<= 1 h_286))) (exists ((h_285 Int)) (<= 1 h_285))) (exists ((h_284 Int)) (<= 1 h_284))) (<= 0 na)) (<= 1 h)) (<= 0 nb)) (<= 0 nc)) (<= 0 nd))))
(assert (= flted_139_11527 (+ (+ (+ (+ nd na) 3) nc) nb)))
(assert (= flted_139_11525 (+ h 2)))
;Negation of Consequence
(assert (not false))
(check-sat)