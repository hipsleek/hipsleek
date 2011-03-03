/**
 Example: array sorting.
 **/

// Identical except between i & j
relation idexc(int[] a, int[] b, int i, int j) == forall(k : (i<=k & k<=j | a[k] = b[k])).

// Membership
//relation member(int[] a, int i, int j, int x) == exists(k : i<=k & k<=j & a[k] = x). 
 
//relation sorted(int[] a, int i, int j) == (i >= j | forall (k : (k < i | k >= j | a[k] <= a[k+1]))).
//relation sorted(int[] a, int i, int j) == (i >= j | i < j & a[i] <= a[i+1] & sorted(a,i+1,j)).
relation sorted(int[] a, int i, int j) == (i >= j | i < j & a[j-1] <= a[j] & sorted(a,i,j-1)).

//Upper bound
//relation upperbnd(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | a[k] <= s))).

//Upper bound preserving: if s is an upper bound of a[i..j] then s is also an upper bound of b[i..j] 
relation upperbndprev(int[] a, int[] b, int i, int j) == forall(s : (!(upperbnd(a,i,j,s)) | upperbnd(b,i,j,s))). 

// Smallest index that gives maximum value in the array 

int array_index_of_max(int[] a, int i, int j)
	requires i>=0 & j>=0 // without this assumption, there might be confusion of the return value
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

relation idexptwopts(int[] a, int[] b, int i, int j) == forall(k : (k = i | k = j | a[k] = b[k])).

void swapelm(ref int[] a, int i, int j)
requires true
ensures a'[i] = a[j] & a'[j] = a[i] & idexptwopts(a,a',i,j);
{
int temp = a[i];
a[i] = a[j];
a[j] = temp;
}


void selection_sort(ref int[] a, int i, int j)
	requires 0<=i & 0<=j
	ensures sorted(a',i,j) & idexc(a',a,i,j) & upperbndprev(a,a',i,j);
{
	if (i < j)
	{
		int k = array_index_of_max(a,i,j);
		
		// swap a[k] & a[j] ==> a[j] now hold the maximum
swapelm(a,k,j);
		
		// sort the remaining part
		selection_sort(a, i, j-1);
	}
}

/**void insertion_sort(ref int[] a, int n)
	requires 0 <= n
	ensures sorted(a',0,n-1);
{
	int k = 1;
	while (k < n)
		requires 1 <= k & sorted(a,0,k-1)
		ensures k' = n & sorted(a',0,k'-1);
	{
		// determine the position to put a[k] so that a[0..k] is sorted
		int j = k;
		while (0 <= j && a[k] < a[j-1])
			requires 0 <= j & j <= k & sorted(a,0,k-1) & strlowerbnd(a, j, k-1, a[k])
			ensures 0 <= j' & j' <= k & upperbnd(a,0,j'-1,a[k]) & strlowerbnd(a,j',k-1,a[k]);
		{ 
			j = j - 1;
		}
		
		// shift the array a[j..k-1] to a[j+1..k] and assign a[j] = a[k]
		int t = a[k];
		int l = j;
		while (l < k)
			requires sorted(a, j+1, l)
			ensures sorted(a', j+1, k);
		{
			a[l+1] = a[l];
		}
		a[j] = t;
		
		// increment k for the next round
		k = k + 1;		
	}
}**/