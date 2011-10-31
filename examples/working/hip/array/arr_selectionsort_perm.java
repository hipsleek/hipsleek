/**
 Example: array sorting using selection sort.
 **/

relation idexc(int[] a, int[] b, int i, int j) == 
	forall(k : (i<=k & k<=j | a[k] = b[k])).

relation sorted(int[] a, int i, int j) == 
	(i >= j | forall (k : (k < i | k >= j | a[k] <= a[k+1]))).

relation upperbnd(int[] a, int i, int j, int s) == 
	(i > j | forall ( k : (k < i | k > j | a[k] <= s))).

relation upperbndprev(int[] a, int[] b, int i, int j) == 
	forall(s : (!(upperbnd(a,i,j,s)) | upperbnd(b,i,j,s))).

relation permutation(int[] a, int[] b, int i, int j).

axiom true ==> permutation(a,a,i,j).

// Reflexivity
axiom i <= j & forall(k : k < i | k > j | a[k] = b[k])  ==> permutation(a,b,i,j).

// Symmetry
axiom permutation(a,b,i,j) ==> permutation(b,a,i,j).

// Transitivity
axiom permutation(a,b,i,j) & permutation(b,c,i,j) ==> permutation(a,c,i,j).

// Composition of two disjoint permutations 
axiom permutation(a,b,i,j) & permutation(a,b,j,k) ==> permutation(a,b,i,k).

// Extensionality : special case of composition
// This special case is necessary to prove insertion sort
axiom permutation(a,b,i,j) & a[j+1] = b[j+1] ==> permutation(a,b,i,j+1).

// Transposition
axiom forall(k : (k = i | k = j | a[k] = b[k])) & a[i] = b[j] & a[j] = b[i] & u <= i <= v & u <= j <= v ==> permutation(a,b,u,v).

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
	ensures dom(a',h,t) & sorted(a',i,j) & idexc(a',a,i,j) & upperbndprev(a,a',i,j) & permutation(a,a',i,j);
{
	if (i < j)
	{
		int k = array_index_of_max(a,i,j);
		int temp = a[k];
		a[k] = a[j];
		a[j] = temp;
		assert permutation(a,a',i,j);
		assume permutation(a,a',i,j);
		assert upperbnd(a',i,j-1,temp');
		assume upperbnd(a',i,j-1,temp');
		selection_sort(a, i, j-1);
	}
}
