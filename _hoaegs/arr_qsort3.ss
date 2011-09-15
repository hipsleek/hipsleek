/**
 Example: Quicksort
 **/

// locations outside i,j are unchanged
relation idexc(int[] a, int[] b, int i, int j) == forall(k : (i<=k & k<=j | a[k] = b[k])).

// locations between i,j are sorted
relation sorted(int[] a, int i, int j) == (i >= j  | i<j & forall (k : (k < i | k >= j | a[k] <= a[k+1]))).

// s is an upper bound for i,j
relation strupperbnd(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | a[k] < s))).

// s is a lower bound for i,j
relation strlowerbnd(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | a[k] > s))).

// locations between i,j each has value s
relation alleqs(int[] a, int i, int j, int s) == (i > j | i<=j & forall ( k : (k < i | k > j | a[k] = s))).

relation upperbndprev(int[] a, int[] b) == forall(i,j,s : (!(strupperbnd(a,i,j,s)) | strupperbnd(b,i,j,s))).

relation lowerbndprev(int[] a, int[] b) == forall(i,j,s : (!(strlowerbnd(a,i,j,s)) | strlowerbnd(b,i,j,s))).

// low,high are the lower and upper bound for i,j
relation bnd(int[] a, int i, int j, int low, int high) == (i > j | i<=j & forall ( k : (k < i | k > j | low <= a[k] <= high))).

// FUNCTION arraypart
// Partition the array a[i..j] into three parts
// a[i..k] contains elements < x
// a[k+1..t-1] contains only x's.
// a[t..j] contains elements > x 

  void arraypart(ref int[] a, int i, int j, int x, ref int k, ref int t)
	case {
		i > j  -> ensures k' = i - 1 & t' = j + 1 & a' = a;
		i <= j -> requires [l,h] bnd(a,i,j,l,h)
                  ensures i - 1 <= k'  & k' <= j & bnd(a', i, k', l,x-1) & alleqs(a', k'+1, t'-1, x) & i <= t' & t' <= j + 1 
                   & bnd(a', t', j, x+1,h) & idexc(a', a, i, j) & bnd(a',i,j,l,h);
	} //'

// i,k --> l,x-1
// t,j --> x+1,h

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

	case {
		i >= j -> ensures a=a';
        i < j -> requires [l,h] bnd(a,i,j,l,h)
          ensures  bnd(a',i,j,l,h) & sorted(a',i,j) & idexc(a',a,i,j);
    }

{
	if (i < j)
	{
		int k, t;
        int x =a[i];
		arraypart(a, i, j, x, k, t);
// i,k --> l,x-1
// t,j --> x+1,h
		qsort(a, i, k); /* l,x-1 */
		qsort(a, t, j); /* x+1,h */
	}
}
