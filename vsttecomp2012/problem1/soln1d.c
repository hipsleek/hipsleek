// a <= b if and only if a = b or a = false & b = true
relation lessthaneq(bool a, bool b) == !a | b.

// A and B are identical except in the domain [i..j]
relation idout(bool[] A, bool[] B, int i, int j) ==
	forall(k : i <= k <= j | A[k] = B[k]).

// A[i..j] is sorted
relation sorted(bool[] A, int i, int j) ==
	forall(k : k < i | k >= j | lessthaneq(A[k],A[k+1])).

// A[i..j] and B[i..j] are permutations of each other
// We are using constructive/recursive definition. It can
// be seen that this definition captures the class of all
// permutations; and thus, everything provable is provable
// using this definition alone.
relation permutation(bool[] A, bool[] B, int i, int j) ==
	// base case : empty array
	i > j 	
	// reflexivity
	| forall(k : k < i | k > j | A[k] = B[k])
	// left extensionality 	
	| permutation(A,B,i+1,j) & A[i] = B[i] 
	// right extensionality
	| permutation(A,B,i,j-1) & A[j] = B[j]
	// transposition
	| permutation(A,B,i+1,j-1) & A[i] = B[j] & A[j] = B[i]
	// transitivity
	| exists(C : permutation(A,C,i,j) & permutation(C,B,i,j)).

void two_way_sort(ref bool[] a, int n)
	requires domb(a,0,n-1)
	ensures sorted(a',0,n-1) & permutation(a,a',0,n-1);
{
	two_way_sort_helper(a, 0, n-1);
}

void two_way_sort_helper(ref bool[] a, int i, int j)
	variance (1) [j-i]
	requires domb(a,i,j)
	ensures sorted(a',i,j) & idout(a,a',i,j) & permutation(a,a',i,j);
{
	if (i <= j) {
		bool b = a[i];
		if (!b)
			two_way_sort_helper(a, i + 1, j);
		else if (a[j])
			two_way_sort_helper(a, i, j - 1);
		else {
			bool t = a[i];
			a[i] = a[j];
			a[j] = t;
			
//			bool[] a1 = a;
//			assert permutation(a, a1', i, j);
//			assume permutation(a, a1', i, j);
			
			two_way_sort_helper(a, i + 1, j - 1);
			
//			assert permutation(a1', a', i , j);
//			assume permutation(a1', a', i , j);
		}
	}
}
