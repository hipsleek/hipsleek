/**
 * Search an array for zero. See why3's example for more
 * details. We need induction to prove the generalization
 * of the property. Compare with binary search.
 * 
 * Reference: "Searching a zero in an array where values 
 * never decrease by more than one" at 
 * http://proval.lri.fr/gallery/decrease1.en.html
 * 
 * @author Vu An Hoa
 */

relation alldiff(int[] a, int x, int i, int j) ==
	forall(k : k < i | k > j | a[k] != x).

// Either use this definition + induction
relation unitdec(int[] a, int i, int j) ==
	forall(k, t: k < i | k >= j | a[k+1] >= a[k] - 1).
				
// Or use the generalized property that we know!
//relation unitdec(int[] a, int i, int j) ==
//	forall(k, t: k < i | k > j | t < i | t > j | k > t | 
//			a[t] >= a[k] - (t - k)).

bool searchzero(int[] a, int i, int j, ref int k)
	requires [al,ah] dom(a,al,ah) & al <= i & j <= ah 
				& unitdec(a, i, j) & induce(j - i)
	ensures res & i <= k' <= j & a[k'] = 0 or 
				!res & alldiff(a, 0, i, j);
{
	if (i <= j) {
		if (a[i] == 0) {
			k = i;
			return true;
		} 
		else if (a[i] > 0)
			return searchzero(a, i + a[i], j, k);
		else 
			return searchzero(a, i+1, j, k);
	} else
		return false;
}
