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
relation unitdec1(int[] a, int i, int j) ==
	forall(k : k < i | k >= j | a[k+1] >= a[k] - 1).
				
// Or use the generalized property that we know!
relation unitdec2(int[] a, int i, int j) ==
	forall(k, t: k < i | k > j | t < i | t > j | k > t | 
			a[t] >= a[k] - (t - k)).
    /*
/*checkentail unitdec1(a,i,i) |- unitdec2(a,i,i).

checkentail !(unitdec1(a,i,j)) |- !(unitdec1(a,i,j+1)).

checkentail (!(unitdec1(a,i,j)) | unitdec2(a,i,j)) & unitdec1(a,i,j+1) |- unitdec2(a,i,j+1).
*/
bool searchzero(int[] a, int i, int j, ref int k)
	requires [al,ah] dom(a,al,ah) & al <= i & j <= ah 
				& unitdec1(a, i, j)
	ensures res & i <= k' <= j & a[k'] = 0 or 
				!res & alldiff(a, 0, i, j);
{
	if (i <= j) {
		//assume a[i] > 0;
		if (a[i] == 0) {
			k = i;
			return true;
		} 
		else if (a[i] > 0) {
			//dprint;
      //assert unitdec2(a, i, j);
      //assume unitdec2(a, i, j);
			bool result = searchzero(a, i + a[i], j, k);
			assert result' & i <= k' <= j & a[k'] = 0 or !result' & alldiff(a, 0, i, j);
			return searchzero(a, i + a[i], j, k);
        }
		else
			return searchzero(a, i+1, j, k);
	} else
		return false;
}
