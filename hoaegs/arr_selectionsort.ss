/**
 Example: array sorting using selection sort.
 **/

// Identical except between i & j
relation idexc(int[] a, int[] b, int i, int j) == forall(k : (i<=k & k<=j | a[k] = b[k])).

relation sorted(int[] a, int i, int j) == (i >= j | forall (k : (k < i | k >= j | a[k] <= a[k+1]))).
//relation sorted(int[] a, int i, int j) == (i >= j | i < j & a[i] <= a[i+1] & sorted(a,i+1,j)).
//relation sorted(int[] a, int i, int j) == (i >= j | i < j & a[j-1] <= a[j] & sorted(a,i,j-1)).

//Upper bound
relation upperbnd(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | a[k] <= s))).

//Upper bound preserving: if s is an upper bound of a[i..j] then s is also an upper bound of b[i..j] 
relation upperbndprev(int[] a, int[] b, int i, int j) == forall(s : (!(upperbnd(a,i,j,s)) | upperbnd(b,i,j,s))).

// x occurs in a[i..j] for s times
relation freq(int[] a, int i, int j, int x, int s) == 
(i > j & s = 0 | a[i] != x & freq(a, i+1, j, x, s) | a[i] = s & freq(a, i+1, j, x, s-1)).

// a[i..j] and b[s..t] are permutations of each other <==> for all x, the number of occurences of x in a[i..j] is identical to the number of occurences of x in b[i..j]
relation arrayperm(int[] a, int i, int j, int[] b, int m, int n) == forall(x, s, t : (!(freq(a, i, j, x, s)) | !(freq(b, m, n, x, t)) | s = t)).

// Smallest index that gives maximum value in the array
int array_index_of_max(int[] a, int i, int j)
	requires i>=0 & j>=0
	case {
		i > j -> ensures res = -1;
		i <= j -> ensures i <= res & res <= j & upperbnd(a, i, j, a[res]);
	}
{
	int k = -1;
	if (i <= j)
	{
		k = array_index_of_max(a,i+1,j);
		if (k == -1 || a[i] >= a[k]) k = i;
	}
	return k;
}

void selection_sort(ref int[] a, int i, int j)
	requires 0<=i & 0<=j
	ensures sorted(a',i,j) & idexc(a',a,i,j) & upperbndprev(a,a',i,j); // & arrayperm(a',i,j,a,i,j);
{
	if (i < j)
	{
		int k = array_index_of_max(a,i,j);
		// swap a[k] & a[j] so that a[j] now hold the maximum
		int temp = a[k];
		a[k] = a[j];
		a[j] = temp;
		// and sort the remaining part
		assert upperbnd(a',i,j-1,temp');
		assume upperbnd(a',i,j-1,temp');
		selection_sort(a, i, j-1);
		// Z3 fail to see that upperbnd(a,i,j-1,temp)!
		// Z3 can prove upperbnd(a,i,j-1,temp), but it does not know that it should prove this property!
		// After proving that the resulting array is sorted, it can add that to the hypothesis to derive a'[j] = a[j] = max a = max a' and hence, prove the upper bound preserving property.
	}
}

/* void selection_sort_b(ref int[] a, int i, int j)
	requires 0<=i & 0<=j
	ensures upperbnd(a,i,j,a'[j]) & upperbnd(a',i,j,a'[j]) & sorted(a',i,j) & idexc(a',a,i,j) & upperbndprev(a,a',i,j);
{
	if (i < j)
	{
		int k = array_index_of_max(a,i,j);
		// swap a[k] & a[j] so that a[j] now hold the maximum
		int temp = a[k];
		a[k] = a[j];
		a[j] = temp;
		// and sort the remaining part
		selection_sort_b(a, i, j-1);
	}
} */
