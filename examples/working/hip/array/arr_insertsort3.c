/**
 * Array sorting using insertion sort.
 * With permutation checking.
 * 
 * @author Vu An Hoa
 */

relation idexc(int[] a, int[] b, int i, int j) == 
	forall(k : (i<=k & k<=j | a[k] = b[k])).

relation sorted(int[] a, int i, int j) == 
	(i >= j | forall (k : (k < i | k >= j | a[k] <= a[k+1]))).

relation permutation(int[] a, int[] b, int i, int j).

axiom true ==> permutation(a,a,i,j).

// Reflexivity
axiom i <= j & forall(k : k < i | k > j | a[k] = b[k])  ==> permutation(a,b,i,j).

// Symmetry
axiom permutation(a,b,i,j) ==> permutation(b,a,i,j).

// Transitivity
axiom permutation(a,b,i,j) & permutation(b,c,i,j) ==> permutation(a,c,i,j).

// Composition of two disjoint permutations 
axiom permutation(a,b,i,j) & permutation(a,b,j+1,k) ==> permutation(a,b,i,k).

// Extensionality : special case of composition
// This special case is necessary to prove insertion sort
axiom permutation(a,b,i,j) & a[j+1] = b[j+1] ==> permutation(a,b,i,j+1).

// Transposition
axiom forall(k : (k = i | k = j | a[k] = b[k])) & a[i] = b[j] & a[j] = b[i] & u <= i <= v & u <= j <= v ==> permutation(a,b,u,v).

/* Sort a[0..n] using Insertion sort algorithm */
void insertion_sort(ref int[] a, int n)
	requires [t] dom(a,0,t) & n<=t
	ensures dom(a',0,t) & sorted(a',0,n) & idexc(a,a',0,n) & permutation(a,a',0,n);
{
	if (n > 0) {
		insertion_sort(a,n-1);
		
		//assert a[n] = a'[n];
		//assert permutation(a,a',0,n-1); // why this fail?
		//assert permutation(a,a',0,n);
		//assume permutation(a,a',0,n);
		
		insertelm(a,n);
	}
}

void insertelm(ref int[] a, int n)
	requires [t] dom(a,0,t) & 0 <= n & n <= t & sorted(a,0,n-1)
	case {
		n <= 0 -> ensures a'=a & dom(a',0,t);
		n > 0 -> ensures dom(a',0,t) & sorted(a',0,n) & idexc(a,a',0,n) & (a'[n] = a[n] | a'[n] = a[n-1]) & permutation(a,a',0,n); //'
	}
{
	if (n > 0) { 
		if (a[n] < a[n-1]) {
			// swap the two elements
			int temp = a[n];
			a[n] = a[n-1];
			a[n-1] = temp;

			// checking that after swapping a[n] and a[n-1], the
			// resulting array is a permutation of the original array
			//assert permutation(a,a',0,n);
			//assume permutation(a,a',0,n);

			insertelm(a,n-1);
		}
	}
}

void swap(ref int[] a, int i, int j) 
	requires [t,k] dom(a,t,k) & t <= i <= k & t <= j <= k
	case {
		i <= j -> ensures dom(a',t,k) & permutation(a,a',i,j);
		i > j -> ensures dom(a',t,k) & permutation(a,a',j,i);
	}
{
	int temp = a[i];
	a[i] = a[j];
	a[j] = temp;
}

