/**
 * Bubble sort example
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
axiom permutation(a,b,i,j) & permutation(a,b,j,k) ==> permutation(a,b,i,k).

// Extensionality : special case of composition
// This special case is necessary to prove insertion sort
axiom permutation(a,b,i,j) & a[j+1] = b[j+1] ==> permutation(a,b,i,j+1).
axiom permutation(a,b,i,j) & a[i-1] = b[i-1] ==> permutation(a,b,i-1,j).

// Transposition
axiom forall(k : (k = i | k = j | a[k] = b[k])) & a[i] = b[j] & a[j] = b[i] & u <= i <= v & u <= j <= v ==> permutation(a,b,u,v).

// Sort the array using bubble sort algorithm: Transpose
// adjacent elements until no transposition is required.
void bubblesort(ref int[] a, int i, int j)
	requires [k,t] dom(a, k, t) & k <= i & j <= t
	ensures sorted(a', i, j) & permutation(a,a',i,j) & idexc(a,a',i,j);
{
	if (!bubble(a, i, j))
		bubblesort(a, i, j);
}

// Go through array a[i..j] once and swap adjacent 
// elements if they are out of increasing order
// return true if no swap is required (in such case
// a[i..j] must be sorted; and false otherwise
bool bubble(ref int[] a , int i , int j)
	requires [k,t] dom(a, k, t) & k <= i & j <= t
	ensures dom(a', k, t) & (!res | sorted(a,i,j) & a' = a) 
				& permutation(a,a',i,j) & idexc(a,a',i,j);
{
	if (i < j)
	{
		/*
		if (a[i] > a[i+1])
		{
			int t = a[i];
			a[i] = a[i+1];
			a[i+1] = t;
			assert permutation(a,a',i,j);
			bubble(a,i+1,j);
			return false;
		}
		else
			return bubble(a,i+1,j);
		*/
		bool out_of_order = (a[i] > a[i+1]);
		if (out_of_order) {
			int t = a[i];
			a[i] = a[i+1];
			a[i+1] = t;
		}
		// The following intermediate information is necessary to attain
		// the final conclusion using transitivity. Earlier version of Z3
		// can perform automated deduction; but 3.2 fail to do so.
		assert permutation(a,a',i,j);
		assume permutation(a,a',i,j);
		return (bubble(a,i+1,j) && !out_of_order);
	}
	else
		return true;
}


