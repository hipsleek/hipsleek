(set-info :source  loris-7.ddns.comp.nus.edu.sg/~project/hip/) 
;Variables declarations
(declare-fun Anon_14918 () Int)
(declare-fun l_14916 () Int)
(declare-fun bh () Int)
(declare-fun bhl_14919 () Int)
(declare-fun n () Int)
(declare-fun nl_14917 () Int)
(declare-fun v_node_408_2358_primed () Int)
(declare-fun Anon_14922 () Int)
(declare-fun bhr_14923 () Int)
(declare-fun nr_14921 () Int)
(declare-fun r_14920 () Int)
;Relations declarations
;Axioms assertions
;Antecedent
(assert (or (and (and (and (= Anon_14918 0) (<= 2 bhl_14919)) (<= 1 nl_14917)) (> l_14916 0)) (or (and (and (and (< l_14916 1) (= nl_14917 0)) (= bhl_14919 1)) (= Anon_14918 0)) (and (and (and (= Anon_14918 1) (<= 1 bhl_14919)) (<= 1 nl_14917)) (> l_14916 0)))))
(assert (= bh (+ bhl_14919 1)))
(assert (= bhl_14919 bhr_14923))
(assert (> r_14920 0))
(assert (= n (+ (+ nr_14921 1) nl_14917)))
(assert (= v_node_408_2358_primed r_14920))
(assert (or (and (and (and (= Anon_14922 0) (<= 2 bhr_14923)) (<= 1 nr_14921)) (> r_14920 0)) (or (and (and (and (< r_14920 1) (= nr_14921 0)) (= bhr_14923 1)) (= Anon_14922 0)) (and (and (and (= Anon_14922 1) (<= 1 bhr_14923)) (<= 1 nr_14921)) (> r_14920 0)))))
;Negation of Consequence
(assert (not (or (= nr_14921 0) (< r_14920 1))))
(check-sat)