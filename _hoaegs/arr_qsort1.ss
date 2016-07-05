/**
 Example: Quicksort
 **/

relation idexc(int[] a, int[] b, int i, int j) == forall(k : (i<=k & k<=j | a[k] = b[k])).

relation sorted(int[] a, int i, int j) == (i >= j | forall (k : (k < i | k >= j | a[k] <= a[k+1]))).

relation strupperbnd(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | a[k] < s))).

relation strlowerbnd(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | a[k] > s))).

relation alleqs(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | a[k] = s))).

relation upperbndprev(int[] a, int[] b) == forall(i,j,s : (!(strupperbnd(a,i,j,s)) | strupperbnd(b,i,j,s))).

relation lowerbndprev(int[] a, int[] b) == forall(i,j,s : (!(strlowerbnd(a,i,j,s)) | strlowerbnd(b,i,j,s))).

relation bnd(int[] a, int i, int j, int low, int high) == (i > j | forall ( k : (k < i | k > j | low <= a[k] <= high))).
// above could be used to replace both strlowerbnd and strupperbnd.
// is there a need for "strict"? 

// FUNCTION arraypart
// Partition the array a[i..j] into three parts
// a[i..k] contains elements < x
// a[k+1..t-1] contains only x's.
// a[t..j] contains elements > x 

void arraypart(ref int[] a, int i, int j, int x, ref int k, ref int t)
	case {
		i > j -> ensures k' = i - 1 & t' = j + 1 & a' = a;
		i <= j -> ensures i - 1 <= k'  & k' <= j & strupperbnd(a', i, k', x) & alleqs(a', k'+1, t'-1, x) & i <= t' & t' <= j + 1 & strlowerbnd(a', t', j, x) & idexc(a', a, i, j) ; // & upperbndprev(a,a') & lowerbndprev(a,a') ;
	}
{
	if (i <= j)
	{
		if (a[i] < x)
			// Since a[i] is in the correct partition,
			// we only need to partition the rest.
			arraypart(a, i + 1, j, x, k, t);
		else if (a[i] > x)
		{
			// a[i] should be in the third partition,
			// so just swap it with a[j]
			int temp = a[i];
			a[i] = a[j];
			a[j] = temp;
			arraypart(a, i, j - 1, x, k, t);
		}
		else // a[i] == x
		{
			// we cannot decide the position of a[i]
			// hence, delay this task and first partition 
			// the remaining part of the array
			arraypart(a, i + 1, j, x, k, t);

			// after this the array should look like
			// i  i+1 ... k k+1 ... t-1 t ... j
			// x      < x       = x        > x
			// so we swap a[k], a[i] to get
			// i  i+1 ... k-1 k k+1 ... t-1 t ... j
			//        < x     x     = x     > x
			// note that we already know a[i] = x so there is no need to use a temporary variable
			a[i] = a[k];
			a[k] = x;
			k = k - 1;
			// without specifying that k' <= j, we cannot prove the identical outside in this case because it might happen that k > j!
		}
	}
	else 
	{
		// These values are chosen so that the algorithm
		// works in all cases. Note that eventually, we 
		// always reach the state when i > j.
		k = i - 1;
		t = j + 1;
	}
}

void qsort(ref int[] a, int i, int j)
	requires true
	ensures sorted(a',i,j) & idexc(a',a,i,j) & upperbndprev(a,a') & lowerbndprev(a,a');
{
	if (i <= j)
	{
		int k, t;
		arraypart(a, i, j, a[i], k, t);
		qsort(a, i, k);
		qsort(a, t, j);

		// Don't know how to solve this problem!!!
		//assume upperbndprev(a,a') & lowerbndprev(a,a');
	}
}
