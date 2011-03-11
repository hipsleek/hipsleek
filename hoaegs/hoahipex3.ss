/**
 Example: array sorting using insertion sort.
 **/

// Two array are identical except between i & j
relation idexc(int[] a, int[] b, int i, int j) == forall(k : (i<=k & k<=j | a[k] = b[k])).

// Two array are identical except at two points i and j
relation idexptwopts(int[] a, int[] b, int i, int j) == forall(k : (k = i | k = j | a[k] = b[k])).

// The sub-array a[i..j] is sorted: three ways to formulate
// (i) a[k] <= a[k+1] for all k between [i..j-1]
// (ii) a[i] <= a[i+1] & array a[i+1..j] is sorted --- right recursive
// (iii) array a[i..j-1] is sorted & a[j-1] <= a[j] --- right recursive
// Different formulation leads to different provability.

relation sorted(int[] a, int i, int j) == (i >= j | forall (k : (k < i | k >= j | a[k] <= a[k+1]))).
//relation sorted(int[] a, int i, int j) == (i >= j | i < j & a[i] <= a[i+1] & sorted(a,i+1,j)).
//relation sorted(int[] a, int i, int j) == (i >= j | i < j & a[j-1] <= a[j] & sorted(a,i,j-1)).

/*void swapelm(ref int[] a, int i, int j)
	requires true
	ensures a'[i] = a[j] & a'[j] = a[i] & idexptwopts(a,a',i,j);
{
	int temp = a[i];
	a[i] = a[j];
	a[j] = temp;
}*/

// Assume that a[0..n-1] is sorted. We want to insert a[n] between a[0..n-1] (and shift the array) in order to make a[0..n] sorted
void insertelm(ref int[] a, int n)
	requires sorted(a,0,n-1)
	case {
		n <= 0 -> ensures a'=a;
		n > 0 -> ensures sorted(a',0,n) & idexc(a,a',0,n) & (a'[n] = a[n] | a'[n] = a[n-1]);
	}
{
	// n <= 0 or a[n] >= a[n-1] : nothing to do because a[0..n] is already sorted
	/* if (n == 1 && a[1] < a[0]) {
		int t = a[n];
		a[n] = a[n-1];
		a[n-1] = t;
	}
	else */ if (n > 0 && a[n] < a[n-1]) {
		//a[n] is out of place, swap a[n] and a[n-1]: note that a[n-1] is the maximum value amongst a[0..n]
		//swapelm(a,n-1,n);
		// State: H = {sorted(a,0,n-1), n > 0, a[n] < a[n-1]}
		
		int t = a[n];
		a[n] = a[n-1];
		a[n-1] = t;
	
		// Post: H = {sorted(a,0,n-1), n > 0, a[n] < a[n-1], a1[n-1] = a[n], a1[n] = a[n-1], forall k<>n,n-1 : a1[k]=a[k]}
		
		//Note that a[0..n-2] is sorted and a[n] (now located at a[n-1] might be out of place ==> recursively insert a[n]
		// H |- sorted(a1,0,n-2)  :: note that reference to a becomes a1 now
		
		insertelm(a,n-1);
		
		// So we obtain A |- sorted(a',0,n-1) & idexc(a1,a',0,n-1) & a'[n-1] >= a1[n-1] & a'[n-1] >= a[n-2]
		// H = {sorted(a,0,n-1), n > 0, a[n] < a[n-1], a1[n-1] = a[n], a1[n] = a[n-1], forall k<n-1: a1[k]=a[k], sorted(a',0,n-1) & idexc(a1,a',0,n-1) & (a'[n-1] = a1[n-1] | a'[n-1] >= a1[n-2]) }
		// H |- sorted(a',0,n) & idexc(a,a',0,n) & [?] ?
	}
}

/* Sort a[0..n] using Insertion sort algorithm */
void insertion_sort(ref int[] a, int n)
	requires true ensures sorted(a',0,n);
{
	// if n = 0, a[0..0] is already sorted
	// if n < 0, a[0..n] is empty, and hence, is trivially sorted
	if (n > 0) {
		// Sort(a[0..n-1] first
		insertion_sort(a, n-1);

		// and then insert a[n] between the sorted a[0..n-1] to make a[0..n] sorted.
		insertelm(a,n);
	}
}

/*
void insertion_sort_loop(ref int[] a, int n)
	requires 0 <= n
	ensures sorted(a',0,n);
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
}
*/
