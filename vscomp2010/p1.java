/**
 Problem 1 in VSComp 2010: Sum and Maximum
 @author Vu An Hoa
 @date 24/06/2011
 **/

relation sumarr(int[] a, int i, int j, int s) == (i > j & s = 0 | i <= j & sumarr(a,i,j-1,s-a[j])).

//relation sumarr(int[] a, int i, int j, int s) == (i > j & s = 0 | i <= j & sumarr(a,i+1,j,s-a[i])).

relation upperbnd(int[] a, int i, int j, int s) == forall(k : (k < i | k > j | a[k] <= s)).

relation isNatural(int[] a, int i, int j) == forall(k : (k < i | k > j | a[k] >= 0)).
/**
 Main function to compute sum and max
 **/
void compute_sum_max(int[] a, int N, ref int sumout, ref int maxout)
	requires dom(a,0,N-1) & N >= 0
	ensures upperbnd(a,0,N-1,maxout') & sumarr(a,0,N-1,sumout') & sumout' <= maxout' * N;
{
	compute_sum_max_helper(a, N, 0, sumout, 0, maxout);
	dprint; // issue detected: variable is not renamed on input
}

/**
 Helper function to compute max and sum.
 @return the output sumout is the sum of its value at entry and sum_{i=0}^{N-1}{a[i]}
         the output maxout is the maximum of {maxout} U {a[i] | i = 0..N-1}
 **/
void compute_sum_max_helper(int[] a, int N, int si, ref int s, int mi, ref int m)
	requires dom(a,0,N-1) & N >= 0
	ensures upperbnd(a,0,N-1,m') & m' >= mi & sumarr(a,0,N-1,s' - si)
			& s' <= si + m' * N;
{
	if (N > 0)
	{
		if (mi < a[N-1]) 
			mi = a[N-1];
		si = si + a[N-1];
		compute_sum_max_helper(a, N-1, si, s, mi, m);
	}
	else {
		s = si;
		m = mi;
	}
}
