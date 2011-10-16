/**
 * Binary search example.
 * Remark: need to use the general definition of sorted-ness. The
 * definition in sorting algorithms does not work.
 * 
 * @author Vu An Hoa
 */

relation alldiff(int[] a, int x, int i, int j) ==
	forall(k : k < i | k > j | a[k] != x).
	
relation allgreater(int[] a, int x, int i, int j) ==
	forall(k : k < i | k > j | a[k] > x).
	
relation allsmaller(int[] a, int x, int i, int j) ==
	forall(k : k < i | k > j | a[k] < x).
	
relation sorted(int[] a, int i, int j) == 
	forall(k, t : (k < i | k > j | t < i | t > j | a[k] <= a[t])).

// Search for x in a[low..high]
bool binary_search(int[] a, int x, int i, int j, ref int k)
	requires [rl,rh] dom(a,rl,rh) & rl <= i & j <= rh & sorted(a,i,j)
	ensures (res & i <= k' <= j & a[k'] = x | !res & alldiff(a, x, i, j));
{	
	if (i <= j) {
		int m = (i + j) / 2;
		assert i <= m' <= j;
		if (a[m] == x) {
			k = m;
			return true;
		} else if (x < a[m]) {
			assert allgreater(a, x, m', j);
			return binary_search(a, x, i, m - 1, k);
		} else {
			assert allsmaller(a, x, i, m');
			return binary_search(a, x, m + 1, j, k);
		}
	} else
		return false;
}