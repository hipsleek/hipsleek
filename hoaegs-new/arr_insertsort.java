/**
 Example: array sorting using insertion sort.
 **/

relation idexc(int[] a, int[] b, int i, int j) == forall(k : (i<=k & k<=j | a[k] = b[k])).

relation idexptwopts(int[] a, int[] b, int i, int j) == forall(k : (k = i | k = j | a[k] = b[k])).

relation sorted(int[] a, int i, int j) == (i >= j | forall (k : (k < i | k >= j | a[k] <= a[k+1]))).

void insertelm(ref int[] a, int n)
	requires [t] dom(a,0,t) & 0 <= n & n <= t & sorted(a,0,n-1)
	case {
		n <= 0 -> ensures a'=a & dom(a',0,t);
		n > 0 -> ensures dom(a',0,t) & sorted(a',0,n) & idexc(a,a',0,n) & (a'[n] = a[n] | a'[n] = a[n-1]);
	}
{
	if (n > 0) { 
		if (a[n] < a[n-1]) {
			int temp = a[n];
			a[n] = a[n-1];
			a[n-1] = temp;
			insertelm(a,n-1);
		}
	}
}

/* Sort a[0..n] using Insertion sort algorithm */
void insertion_sort(ref int[] a, int n)
	requires [t] dom(a,0,t) & n<=t
	ensures dom(a',0,t) & sorted(a',0,n);
{
	if (n > 0) {
		insertion_sort(a,n-1);
		insertelm(a,n);
	}
}