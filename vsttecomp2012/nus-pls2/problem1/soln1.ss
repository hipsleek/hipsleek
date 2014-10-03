// a <= b if and only if a = b or a = false & b = true
relation lessthaneq(bool a, bool b) == !a | b.

// A and B are identical except in the domain [i..j]
relation idout(bool[] A, bool[] B, int i, int j) ==
	forall(k : i <= k <= j | A[k] = B[k]).

// A[i..j] is sorted
relation sorted(bool[] A, int i, int j) ==
	forall(k : k < i | k >= j | lessthaneq(A[k],A[k+1])).

/* relation freq(bool[] A, int i, int j, bool b, int f) ==
	(i > j & f = 0) | (i <= j & (A[i] = b & freq(A,i+1,j,b,f-1) | A[i] != b & freq(A,i+1,j,b,f))). */

// A[i..j] and B[i..j] are permutations of each other.
relation permutation(bool[] A, bool[] B, int i, int j).

// empty arrays
axiom i > j ==> permutation(A,B,i,j).

// reflexivity
axiom forall(k : k < i | k > j | A[k] = B[k]) ==> permutation(A,B,i,j).

// extensionality
axiom permutation(A,B,i+1,j) & A[i] = B[i] ==> permutation(A,B,i,j).
axiom permutation(A,B,i,j-1) & A[j] = B[j] ==> permutation(A,B,i,j).

// transposition
axiom permutation(A,B,i+1,j-1) & A[i] = B[j] & A[j] = B[i] ==> permutation(A,B,i,j).

// transitivity
axiom permutation(A,B,i,j) & permutation(B,C,i,j) ==> permutation(A,C,i,j).

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
			
			bool[] a1 = a;
			assert permutation(a, a1', i, j);
			assume permutation(a, a1', i, j);
			
			two_way_sort_helper(a, i + 1, j - 1);
			
			assert permutation(a1', a', i , j);
			assume permutation(a1', a', i , j);
		}
	}
}
