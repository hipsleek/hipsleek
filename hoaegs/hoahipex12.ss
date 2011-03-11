/**
 Example: Quicksort
 **/

relation idexc(int[] a, int[] b, int i, int j) == forall(k : (i<=k & k<=j | a[k] = b[k])).

relation sorted(int[] a, int i, int j) == (i >= j | forall (k : (k < i | k >= j | a[k] <= a[k+1]))).

relation strupperbnd(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | a[k] < s))).

relation strlowerbnd(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | a[k] > s))).

relation alleqs(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | a[k] = s))).

// partition the array a[i..j] into three parts
// a[i..k] contains elements < x
// a[k+1..t-1] contains only x's.
// a[t..j] contains elements > x
void arraypart(ref int[] a, int i, int j, int x, ref int k, ref int t)
	requires true
	ensures strupperbnd(a', i, k', x) & alleqs(a', k'+1, t'-1, x) & strlowerbnd(a', t', j, x) & idexc(a', a, i, j);
{
	if (i <= j)
	{
		if (a[i] < x)
			arraypart(a, i + 1, j, x, k, t);
		else if (a[i] > x)
		{
			int t = a[i];
			a[i] = a[j];
			a[j] = t;
			arraypart(a, i, j - 1, x, k, t);
		}
		else // a[i] == x
		{
			// first partition the remaining
			arraypart(a, i + 1, j, x, k, t);
			// swap a[k], a[i] and reduce k
			// note that we already know a[i] = x so there is no need to use a temporary variable
			a[i] = a[k];
			a[k] = x;
			k = k - 1;
		}
	}
	else
	{	// dummy values
		k = i - 1;
		t = k - 1;
	}
}

void qsort(ref int[] a, int i, int j)
	requires true
	ensures sorted(a',i,j) & idexc(a',a,i,j);
{
	if (i <= j)
	{
		int k, t;
		arraypart(a, i, j, a[i], k, t);
		qsort(a, i, k);
		qsort(a, t, j);
	}
}
