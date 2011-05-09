/**
 Example: array sorting using selection sort.
 **/

relation idexc(int[] a, int[] b, int i, int j) == forall(k : (i<=k & k<=j | a[k] = b[k])).

relation sorted(int[] a, int i, int j) == (i >= j | forall (k : (k < i | k >= j | a[k] <= a[k+1]))).

relation upperbnd(int[] a, int i, int j, int s) == (i > j | forall ( k : (k < i | k > j | a[k] <= s))).

relation upperbndprev(int[] a, int[] b, int i, int j) == forall(s : (!(upperbnd(a,i,j,s)) | upperbnd(b,i,j,s))).

// Smallest index that gives maximum value in the array
int array_index_of_max(int[] a, int i, int j)
	requires [k,t] dom(a,k,t) & k <= i & j <= t
	case {
		i > j -> ensures res = i - 1;
		i <= j -> ensures i <= res & res <= j & upperbnd(a, i, j, a[res]);
	}
{
	int k = i - 1;
	if (i <= j)
	{
		k = array_index_of_max(a,i+1,j);
		if (k < i) 
			k = i;
		else if (a[i] >= a[k])
			k = i;
	}
	return k;
}

void selection_sort(ref int[] a, int i, int j)
	requires [h,t] dom(a,h,t) & h<=i & j<=t
	ensures dom(a',h,t) & sorted(a',i,j) & idexc(a',a,i,j) & upperbndprev(a,a',i,j);
{
	if (i < j)
	{
		int k = array_index_of_max(a,i,j);
		int temp = a[k];
		a[k] = a[j];
		a[j] = temp;
		assert upperbnd(a',i,j-1,temp');
		assume upperbnd(a',i,j-1,temp');
		selection_sort(a, i, j-1);
	}
}