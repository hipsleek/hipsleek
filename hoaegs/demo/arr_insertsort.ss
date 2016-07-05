/**
 Example: array sorting using insertion sort.
 **/

// Two array are identical except between i & j
relation idexc(int[] a, int[] b, int i, int j) == forall(k : (i<=k & k<=j | a[k] = b[k])).

relation sorted(int[] a, int i, int j) == (i >= j | forall (k : (k < i | k >= j | a[k] <= a[k+1]))).

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

void insertelm(ref int[] a, int n)
	requires sorted(a,0,n-1)
	case {
		n <= 0 -> ensures a'=a;
		n > 0 -> ensures sorted(a',0,n) & idexc(a,a',0,n) 
					& (a'[n] = a[n] | a'[n] = a[n-1]);

	}
{
	// n <= 0 or a[n] >= a[n-1] : nothing to do because a[0..n] is already sorted
	if (n > 0 && a[n] < a[n-1]) {
		//a[n] is out of place, swap a[n] and a[n-1]: note that a[n-1] is the maximum value amongst a[0..n]
		int t = a[n];
		a[n] = a[n-1];
		a[n-1] = t;
	
		insertelm(a,n-1);
	}
}
