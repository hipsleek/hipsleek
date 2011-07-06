(set-logic AUFNIA)
(declare-fun x_49' () Int)
(declare-fun a () (Array Int Int))
(declare-fun h_834 () Int)
(declare-fun a_865 () (Array Int Int))
(declare-fun k_47' () Int)
(declare-fun x_49 () Int)
(declare-fun u_847 () Int)
(declare-fun v_848 () Int)
(declare-fun l_849 () Int)
(declare-fun a_873 () (Array Int Int))
(declare-fun t_48' () Int)
(declare-fun l_833 () Int)
(declare-fun h_850 () Int)
(declare-fun a' () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun dom ((Array Int Int) Int Int) Bool)
(declare-fun matchinp (Int Int) Bool)
(declare-fun bnd ((Array Int Int) Int Int Int Int) Bool)
(declare-fun alleqs ((Array Int Int) Int Int Int) Bool)
(declare-fun sorted ((Array Int Int) Int Int) Bool)
(declare-fun idexc ((Array Int Int) (Array Int Int) Int Int) Bool)
(declare-fun dom ((Array Int Int) Int Int) Bool)
(assert (forall (a (Array Int Int)) (low Int) (high Int) (= (dom a low high) true)))
(assert (forall (x Int) (y Int) (= (matchinp x y) true)))
(assert (forall (a (Array Int Int)) (i Int) (j Int) (low Int) (high Int) (= (bnd a i j low high) (or (> i j) (and (<= i j) (forall (?k Int) (or (< ?k i) (or (> ?k j) (and (<= low (select a ?k)) (<= (select a ?k) high))))))))))
(assert (forall (a (Array Int Int)) (i Int) (j Int) (s Int) (= (alleqs a i j s) (or (> i j) (and (<= i j) (forall (?k Int) (or (< ?k i) (or (> ?k j) (= (select a ?k) s)))))))))
(assert (forall (a (Array Int Int)) (i Int) (j Int) (= (sorted a i j) (or (>= i j) (and (< i j) (forall (?k Int) (or (< ?k i) (or (>= ?k j) (<= (select a ?k) (select a (+ ?k 1)))))))))))
(assert (forall (a (Array Int Int)) (b (Array Int Int)) (i Int) (j Int) (= (idexc a b i j) (forall (?k Int) (or (and (<= i ?k) (<= ?k j)) (= (select a ?k) (select b ?k)))))))
(assert (forall (a (Array Int Int)) (low Int) (high Int) (= (dom a low high) (or (dom a (- low 1) high) (dom a low (+ high 1))))))
(assert (<= u_847 t_48'))
(assert (dom a_873 u_847 v_848))
(assert (= (+ x_49 1) l_849))
(assert (dom a_873 u_847 v_848))
(assert (<= k_47' v_848))
(assert (dom a_865 u_847 v_848))
(assert (= (- x_49' 1) h_834))
(assert (alleqs a_865 (+ k_47' 1) (- t_48' 1) x_49'))
(assert (dom a_865 u_847 v_848))
(assert (matchinp l_833 h_850))
(assert (dom a u_847 v_848))
(assert (bnd a i j l_833 h_850))
(assert (< i j))
(assert (dom a u_847 v_848))
(assert (<= i v_848))
(assert (= x_49' (select a i)))
(assert (dom a u_847 v_848))
(assert (bnd a i j l_833 h_850))
(assert (<= i (+ k_47' 1)))
(assert (<= k_47' j))
(assert (bnd a_865 i k_47' l_833 (- x_49' 1)))
(assert (<= i t_48'))
(assert (<= t_48' (+ 1 j)))
(assert (bnd a_865 t_48' j (+ x_49' 1) h_850))
(assert (idexc a_865 a i j))
(assert (bnd a_865 i j l_833 h_850))
(assert (<= i j))
(assert (<= u_847 i))
(assert (bnd a_865 i k_47' l_833 h_834))
(assert (bnd a_873 i k_47' l_833 h_834))
(assert (sorted a_873 i k_47'))
(assert (idexc a_873 a_865 i k_47'))
(assert (< i k_47'))
(assert (bnd a_873 t_48' j (+ x_49 1) h_850))
(assert (<= j v_848))
(assert (bnd a_873 t_48' j l_849 h_850))
(assert (dom a' u_847 v_848))
(assert (bnd a' t_48' j l_849 h_850))
(assert (sorted a' t_48' j))
(assert (idexc a' a_873 t_48' j))
(assert (< t_48' j))
(assert (bnd a' i j l_833 h_850))
(assert (not (sorted a' i j)))
(check-sat)

