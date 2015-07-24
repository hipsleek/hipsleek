(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun r_1892 () Int)
(declare-fun flted_25_1887 () Int)
(declare-fun n () Int)
(declare-fun nmin () Int)
(declare-fun nmin2_1893 () Int)
(declare-fun v_node2_71_1463_primed () Int)
(declare-fun flted_25_1888 () Int)
(declare-fun nmin1_1891 () Int)
(declare-fun l_1890 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (<= 1 nmin2_1893) (<= nmin2_1893 flted_25_1887)) (> r_1892 0)) (or (and (and (< r_1892 1) (= flted_25_1887 0)) (= nmin2_1893 0)) (and (and (<= 1 nmin2_1893) (< nmin2_1893 flted_25_1887)) (> r_1892 0)))))
(assert (= (+ flted_25_1887 2) n))
(assert (= (+ flted_25_1888 1) n))
(assert (exists ((min_1909 Int)) (and (= nmin (+ 1 min_1909)) (or (and (= min_1909 nmin1_1891) (< nmin1_1891 nmin2_1893)) (and (= min_1909 nmin2_1893) (>= nmin1_1891 nmin2_1893))))))
(assert (= v_node2_71_1463_primed l_1890))
(assert (or (and (and (<= 1 nmin1_1891) (<= nmin1_1891 flted_25_1888)) (> l_1890 0)) (or (and (and (< l_1890 1) (= flted_25_1888 0)) (= nmin1_1891 0)) (and (and (<= 1 nmin1_1891) (< nmin1_1891 flted_25_1888)) (> l_1890 0)))))
;Negation of Consequence
(assert (not (or (= flted_25_1888 0) (or (= nmin1_1891 0) (< l_1890 1)))))
(check-sat)