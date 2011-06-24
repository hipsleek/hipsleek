/**
 Problem 2 in VSComp 2010: Inverting an Injection
 @author Vu An Hoa
 @date 24/06/2011
 **/

relation dom(int[] a, int i, int j) == true.

relation isInverse(int[] a, int[] b, int i, int j) ==
	forall(k : (k < i | k > j | a[b[k]] = k & b[a[k]] = k)).

relation range(int[] a, int i, int j, int l, int h) ==
	forall(k : (k < i | k > j | l <= a[k] & a[k] <= h)).	

void invert(int[] A, ref int[] B, int N)
	requires dom(A,0,N-1) & dom(B,0,N-1) & range(B,0,N-1,0,N-1)
	ensures isInverse(A,B',0,N-1);
{
	if (N > 0) {
		B[A[N-1]] = N-1;
		invert(A,B,N-1);
	}
}
