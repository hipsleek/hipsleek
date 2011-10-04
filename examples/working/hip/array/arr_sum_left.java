
/**
 * Find the sum of the elements of an array. This examples
 * show two ways of computing the sum and illustrates the use
 * of induction.
 * 
 * @author Vu An Hoa
 */

relation dom(int[] a, int low, int high) == 
	(dom(a,low-1,high) | dom(a,low,high+1)).

relation sumarray(int[] a, int i, int j, int s) == 
	(i > j & s = 0 | i = j & s = a[i] | i < j & sumarray(a,i+1,j,s-a[i])).

int sigmaleft(int[] a, int i, int j) 
	requires [t,k] dom(a,t,k) & t <= i & j <= k & induce(j - i)
	ensures sumarray(a,i,j,res);
{
	if (i > j)
		return 0;
	else 
	{
		return sigmaleft(a, i, j-1) + a[j];
	}
}

/* 
  why are there so many duplicated assertions?
  why are there some redundant assertions?
  Chanh : perhaps slicing could help?

# below contains many duplicated declaration
(set-logic AUFNIA)
(declare-fun v_int_25_629 () Int)
(declare-fun ahalb () Int)
(declare-fun ahaub () Int)
(declare-fun v_int_25_639 () Int)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v_int_25_590' () Int)
(declare-fun dom ((Array Int Int) Int Int) Bool)
(declare-fun induce (Int) Bool)
(declare-fun sumarray ((Array Int Int) Int Int Int) Bool)
(declare-fun dom ((Array Int Int) Int Int) Bool)
(assert (forall (a (Array Int Int)) (low Int) (high Int) (= (dom a low high) true)))
(assert (forall (value Int) (= (induce value) true)))
(assert (forall (a (Array Int Int)) (i Int) (j Int) (s Int) (= (sumarray a i j s) (or (and (> i j) (= s 0)) (or (and (= i j) (= s (select a i))) (and (< i j) (sumarray a (+ i 1) j (- s (select a i)))))))))
(assert (forall (a (Array Int Int)) (low Int) (high Int) (= (dom a low high) (or (dom a (- low 1) high) (dom a low (+ high 1))))))
(assert (<= v_int_25_629 ahaub))
(assert (dom a ahalb ahaub))
(assert (induce (- j i)))
(assert (<= i j))
(assert (= (+ v_int_25_629 1) j))
(assert (dom a ahalb ahaub))
(assert (<= ahalb i))
(assert (induce (- v_int_25_629 i)))
(assert (sumarray a i v_int_25_629 v_int_25_639))
(assert (dom a ahalb ahaub))
(assert (<= ahalb j))
(assert (<= j ahaub))
(assert (= v_int_25_590' (+ (select a j) v_int_25_639)))
(assert (not (sumarray a i j v_int_25_590')))
(check-sat)

*/
